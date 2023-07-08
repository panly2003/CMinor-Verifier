/*
    TODO: 这是你唯一允许编辑的文件，你可以对此文件作任意的修改，只要整个项目可以正常地跑起来。
*/

using System.IO;
using System.Collections.Generic;

namespace cminor
{
    /// <summary> 一个验证器，接受一个中间表示，判断其是否有效。 </summary>
    class Verifier
    {
        SMTSolver solver = new SMTSolver();
        TextWriter writer;

        public Verifier(TextWriter writer)
        {
            this.writer = writer;
        }

        /// <summary> 应用此验证器 </summary>
        /// <param name="cfg"> 待验证的控制流图 </param>
        /// <returns> 验证结果 </returns>
        /// <list type="bullet">
        ///     <item> “&gt; 0” 表示所有的 specification 都成立 </item>
        ///     <item> “&lt; 0” 表示有一个 specification 不成立 </item>
        ///     <item> “= 0” 表示 unknown </item>
        /// </list>

        public List<List<Location>> find_basic_paths(Function func)
        {
            Location root = func.entryLocation;
            // 初始化
            List<List<Location>> basic_paths = new List<List<Location>>();
            Stack<Location> locations_stack = new Stack<Location>();
            Stack<List<Location>> unfinished_paths_stack = new Stack<List<Location>>();
            Stack<List<Location>> loop_locations_stack = new Stack<List<Location>>();

            locations_stack.Push(root);

            List<Location> initial_path = new List<Location>();
            initial_path.Add(root);
            unfinished_paths_stack.Push(initial_path);

            List<Location> none_location = new List<Location>();
            loop_locations_stack.Push(none_location);

            // 处理entrylocation后继为空的情况
            if(root.succLocations.Count == 0){
                if(func.locations.Count == 0){
                    Location loc = new ExitLocation();
                    root.succLocations.Add(loc);
                    root.succStatements.Add(new AssumeStatement{condition = new BoolConstantExpression(true)});
                }
                else{
                    root.succLocations.Add(func.locations[0]);
                    root.succStatements.Add(new AssumeStatement{condition = new BoolConstantExpression(true)});
                }
            }

            // dfs
            while(locations_stack.Count != 0){
                int flag = 0;
                Location cur_location = locations_stack.Pop();
                List<Location> cur_unfinished_path = unfinished_paths_stack.Pop();
                List<Location> cur_loop_locations = loop_locations_stack.Pop();

                // 抽出cur_location的succStatements以备检查是否有函数调用
                List<Statement> succ_statements = cur_location.succStatements;
                foreach(Statement stmt in succ_statements){
                    if(stmt is FunctionCallStatement){
                        flag = 1;
                        break;
                    }
                }

                // 处理函数调用
                if(flag == 1){
                    basic_paths.Add(cur_unfinished_path); // 当前路径结束，加入基本路径列表
                    // 对当前状态所有的后继位置，压入位置栈，并分别将它们加到cur_unfinished_path后面重新压入路径栈
                    foreach(Location succ_location in cur_location.succLocations){
                        locations_stack.Push(succ_location);

                        List<Location> new_path = new List<Location>(cur_unfinished_path);
                        new_path.Add(succ_location);
                        unfinished_paths_stack.Push(new_path);

                        loop_locations_stack.Push(cur_loop_locations);
                    }
                }

                // 处理函数结束
                else if(cur_location is ExitLocation){
                    basic_paths.Add(cur_unfinished_path); // 当前路径结束，加入基本路径列表
                }

                // 处理第一次遇到一个新的循环头
                else if(cur_location is LoopHeadLocation && !(cur_loop_locations.Contains(cur_location))){
                    basic_paths.Add(cur_unfinished_path); // 当前路径结束，加入基本路径列表
                    // 对当前状态所有的后继位置，压入位置栈，并以分别以它们为第二个位置建立新path压入路径栈
                    foreach(Location succ_location in cur_location.succLocations){
                        locations_stack.Push(succ_location);

                        List<Location> new_path = new List<Location>();
                        new_path.Add(cur_location);
                        new_path.Add(succ_location);
                        unfinished_paths_stack.Push(new_path);

                        List<Location> new_loop_locations = new List<Location>(cur_loop_locations);
                        new_loop_locations.Add(cur_location);
                        loop_locations_stack.Push(new_loop_locations);

                    }
                }

                // 处理循环返回到循环头了
                else if(cur_location is LoopHeadLocation && cur_loop_locations.Contains(cur_location)){
                    basic_paths.Add(cur_unfinished_path); // 当前路径结束，加入基本路径列表
                }

                // default
                else{
                    // 对当前状态所有的后继位置，压入位置栈，并分别将它们加到cur_unfinished_path后面重新压入路径栈
                    foreach(Location succ_location in cur_location.succLocations){
                        locations_stack.Push(succ_location);

                        List<Location> new_path = new List<Location>(cur_unfinished_path);
                        new_path.Add(succ_location);
                        unfinished_paths_stack.Push(new_path);

                        loop_locations_stack.Push(cur_loop_locations);
                    }
                }

            }


            return basic_paths;
        }


        public int Apply(IRMain cfg)
        {
            // step 1: 将所有的谓词定义写入solver
            if(cfg.predicates.First != null){
                LinkedListNode<Predicate> cur_node = cfg.predicates.First;
                while(true){
                    solver.definePredicate(cur_node.Value);
                    if(cur_node.Next != null){
                        cur_node = cur_node.Next;
                    }
                    else{
                        break;
                    }
                }
            }

            // step 2: dfs搜索基本路径
            foreach(Function func in cfg.functions){
                // Location root = func.entryLocation;
                List<List<Location>> basic_paths = find_basic_paths(func);

                // step 3: 对每条基本路径，求验证条件
                foreach(List<Location> basic_path in basic_paths){
                    // 给出前置条件和入口秩函数
                    Location start_location = basic_path[0];
                    Expression pre_condition = new BoolConstantExpression(true);
                    List<Expression> entry_ranking_funcs = ((HeadLocation)start_location).rankingFunctions;
                    foreach(Expression entry_ranking_func in entry_ranking_funcs){
                        if(entry_ranking_func is NegExpression){
                            return -1;
                        }
                    }

                    if(start_location is EntryLocation){
                        foreach(Expression condition in ((EntryLocation)start_location).conditions)
                        {
                            pre_condition = new AndExpression(pre_condition, condition);
                        }
                    }
                    else if(start_location is LoopHeadLocation){
                        foreach(Expression invariant in ((LoopHeadLocation)start_location).invariants)
                        {
                            pre_condition = new AndExpression(pre_condition, invariant);
                        }
                    }
                    else{
                        // writer.Write("gg1\n");
                    }
                    
                    // 给出后置条件和出口秩函数
                    Location end_location = basic_path[basic_path.Count - 1];
                    Expression post_condition = new BoolConstantExpression(true);
                    List<Expression> exit_ranking_funcs = new List<Expression>();
                    if(end_location is LoopHeadLocation){
                        foreach(Expression invariant in ((LoopHeadLocation)end_location).invariants)
                        {
                            post_condition = new AndExpression(post_condition, invariant);
                        }
                        exit_ranking_funcs = new List<Expression>(((HeadLocation)end_location).rankingFunctions);
                    }
                    else if(end_location is ExitLocation){
                        foreach(Expression condition in ((ExitLocation)end_location).conditions)
                        {
                            post_condition = new AndExpression(post_condition, condition);
                        }
                    }
                    else{ // 函数调用
                        List<Statement> succ_statements = end_location.succStatements;
                        foreach(Statement succ_statement in succ_statements){
                            if(succ_statement is FunctionCallStatement){
                                FunctionCallStatement func_call_stmt = (FunctionCallStatement)succ_statement;
                                Function callee = func_call_stmt.rhs.function;
                                foreach(Expression condition in callee.entryLocation.conditions){
                                    post_condition = new AndExpression(post_condition, condition);
                                }
                                exit_ranking_funcs = new List<Expression>(((HeadLocation)callee.entryLocation).rankingFunctions);
                                // 变量替换
                                if(func_call_stmt.rhs.argumentVariables.Count != callee.parameters.Count){
                                    // writer.Write("gg4\n");
                                }
                                for(int n = 0; n < func_call_stmt.rhs.argumentVariables.Count; n++){
                                    post_condition = post_condition.Substitute(callee.parameters[n], new VariableExpression(func_call_stmt.rhs.argumentVariables[n]));
                                }
                                for(int m = 0; m < exit_ranking_funcs.Count; m++){
                                    for(int n = 0; n < func_call_stmt.rhs.argumentVariables.Count; n++){
                                        exit_ranking_funcs[m] = exit_ranking_funcs[m].Substitute(callee.parameters[n], new VariableExpression(func_call_stmt.rhs.argumentVariables[n]));
                                    }
                                }
                            }
                        }
                    }

                    // debug: 打印前后置条件 + 基本路径
                    writer.Write("path: \n");
                    pre_condition.Print(writer);
                    writer.Write("\n");
                    foreach(Location loc in basic_path){
                        loc.Print(writer);
                    }
                    post_condition.Print(writer);
                    writer.Write("\n");
                    

                    // 验证部分正确性
                    Expression cur_post_condition = post_condition; // 部分正确性

                    int idx = basic_path.Count - 2;
                    while(idx >= 0){
                        Location cur_location = basic_path[idx];
                        List<Statement> succ_statements = cur_location.succStatements;
                        List<Location> succ_locations = cur_location.succLocations;
                        // 找到该路径对应的succ_statement
                        int i = succ_locations.IndexOf(basic_path[idx + 1]);
                        Statement cur_statement = succ_statements[i];
                        writer.Write(cur_statement.GetType());
                        writer.Write("\n");

                        // 部分正确性
                        if(cur_statement is VariableAssignStatement){
                            cur_post_condition = cur_post_condition.Substitute(((VariableAssignStatement)cur_statement).variable, ((VariableAssignStatement)cur_statement).rhs);
                        }
                        else if(cur_statement is AssumeStatement){
                            cur_post_condition = new ImplicationExpression(((AssumeStatement)cur_statement).condition, cur_post_condition);
                        }
                        else if(cur_statement is SubscriptAssignStatement){
                            SubscriptAssignStatement stmt = ((SubscriptAssignStatement)cur_statement);
                            VariableExpression array_exp = new VariableExpression(stmt.array);
                            VariableExpression array_len = new VariableExpression(stmt.array.length);
                            ArrayUpdateExpression new_expr = new ArrayUpdateExpression(array_exp, stmt.subscript, stmt.rhs, array_len);
                            cur_post_condition = cur_post_condition.Substitute(stmt.array, new_expr);
                        }
                        else if(cur_statement is FunctionCallStatement){
                            FunctionCallStatement stmt = (FunctionCallStatement) cur_statement;
                            List<Expression> callee_post_conditions = stmt.rhs.function.exitLocation.conditions;
                                
                            // 把被调用函数的后置条件用AndExpression与起来
                            Expression callee_post_condition = new BoolConstantExpression(true);
                            foreach(Expression condition in callee_post_conditions)
                            {
                                callee_post_condition = new AndExpression(callee_post_condition, condition);
                            }
                            callee_post_condition.Print(writer);
                            writer.Write("\n");

                            if(stmt.lhs != null){
                                List<LocalVariable> callee_rtn_vars = stmt.rhs.function.rvs;
                                if(stmt.lhs.Count != callee_rtn_vars.Count){
                                    // writer.Write("gg2\n");
                                }
                                // 形式返回值换成真实返回值
                                for(int n = 0; n < callee_rtn_vars.Count; n++){
                                    callee_post_condition = callee_post_condition.Substitute(callee_rtn_vars[n], new VariableExpression(stmt.lhs[n]));
                                }
                            }
                            // 形参换成实参
                            if(stmt.rhs.argumentVariables.Count != stmt.rhs.function.parameters.Count){
                                // writer.Write("gg5\n");
                            }
                            for(int n = 0; n < stmt.rhs.argumentVariables.Count; n++){
                                callee_post_condition = callee_post_condition.Substitute(stmt.rhs.function.parameters[n], new VariableExpression(stmt.rhs.argumentVariables[n]));
                            }
                            // assume
                            cur_post_condition = new ImplicationExpression(callee_post_condition, cur_post_condition);
                        }
                        else if(cur_statement is AssertStatement){
                            cur_post_condition = new AndExpression(cur_post_condition, ((AssertStatement)cur_statement).pred);
                        }
                        else{
                            // writer.Write("gg3\n");
                        }

                        idx -= 1;
                        cur_post_condition.Print(writer);
                        writer.Write("\n");
                    }

                    // 最终验证条件：pre -> wp
                    Expression check_condition = new ImplicationExpression(pre_condition, cur_post_condition);

                    // 对验证条件做验证，如果非有效式，立即返回-1
                    if(solver.CheckValid(check_condition) != null){
                        return -1;
                    }

                    // 验证终止性 
                    Expression cur_rank_condition; 
                    // 给entry_ranking_funcs中的变量换名
                    if(exit_ranking_funcs.Count != 0){
                        List<Expression> renamed_entry_ranking_funcs = new List<Expression>();
                        List<List<LocalVariable>> unrenamed_variables_list = new List<List<LocalVariable>>();
                        List<List<LocalVariable>> renamed_variables_list = new List<List<LocalVariable>>();
                        int u = 0;
                        for(int n=0; n < entry_ranking_funcs.Count; n++){
                            Expression renamed_entry_ranking_func = entry_ranking_funcs[n];
                            HashSet<LocalVariable> variables = entry_ranking_funcs[n].GetFreeVariables();
                            List<LocalVariable> unrenamed_variables = new List<LocalVariable>();
                            List<LocalVariable> renamed_variables = new List<LocalVariable>();
                            foreach(LocalVariable variable in variables){
                                LocalVariable renamed_variable = new LocalVariable{type = variable.type, name = variable.name + "$r" + u.ToString()};
                                renamed_entry_ranking_func = renamed_entry_ranking_func.Substitute(variable, new VariableExpression(renamed_variable));
                                renamed_variables.Add(renamed_variable);
                                unrenamed_variables.Add(variable);
                                u += 1;
                            }
                            renamed_entry_ranking_funcs.Add(renamed_entry_ranking_func);
                            unrenamed_variables_list.Add(unrenamed_variables);
                            renamed_variables_list.Add(renamed_variables);
                        }


                        // 字典序组装
                        cur_rank_condition = new BoolConstantExpression(false);
                        for(int n=0; n < entry_ranking_funcs.Count; n++){
                            Expression a = new LTExpression(exit_ranking_funcs[n], renamed_entry_ranking_funcs[n]);
                            for(int j=0;j<n;j++){
                                Expression b = new EQExpression(exit_ranking_funcs[j], renamed_entry_ranking_funcs[j]);
                                a = new AndExpression(a, b);
                            }
                            cur_rank_condition = new OrExpression(cur_rank_condition, a);
                        }
                        for(int n=0; n < entry_ranking_funcs.Count; n++){
                            cur_rank_condition = new AndExpression(cur_rank_condition, new GEExpression(exit_ranking_funcs[n], new IntConstantExpression(0))) ;
                        }

                        cur_rank_condition.Print(writer);
                        writer.Write("\n");

                        idx = basic_path.Count - 2;
                        while(idx >= 0){
                            Location cur_location = basic_path[idx];
                            List<Statement> succ_statements = cur_location.succStatements;
                            List<Location> succ_locations = cur_location.succLocations;
                            // 找到该路径对应的succ_statement
                            int i = succ_locations.IndexOf(basic_path[idx + 1]);
                            Statement cur_statement = succ_statements[i];
                            writer.Write(cur_statement.GetType());
                            writer.Write("\n");

                            if(cur_statement is VariableAssignStatement){
                                cur_rank_condition = cur_rank_condition.Substitute(((VariableAssignStatement)cur_statement).variable, ((VariableAssignStatement)cur_statement).rhs);
                            }
                            else if(cur_statement is AssumeStatement){
                                cur_rank_condition = new ImplicationExpression(((AssumeStatement)cur_statement).condition, cur_rank_condition);
                            }
                            else if(cur_statement is SubscriptAssignStatement){
                                SubscriptAssignStatement stmt = ((SubscriptAssignStatement)cur_statement);
                                VariableExpression array_exp = new VariableExpression(stmt.array);
                                VariableExpression array_len = new VariableExpression(stmt.array.length);
                                ArrayUpdateExpression new_expr = new ArrayUpdateExpression(array_exp, stmt.subscript, stmt.rhs, array_len);
                                cur_rank_condition = cur_rank_condition.Substitute(stmt.array, new_expr);
                            }
                            else if(cur_statement is FunctionCallStatement){
                                // 如果cur_statement的localvariable_list不为null，把callee的后置条件 
                                FunctionCallStatement stmt = (FunctionCallStatement) cur_statement;
                                List<Expression> callee_post_conditions = stmt.rhs.function.exitLocation.conditions;
                                    
                                // 把被调用函数的后置条件用AndExpression与起来
                                Expression callee_post_condition = new BoolConstantExpression(true);
                                foreach(Expression condition in callee_post_conditions)
                                {
                                    callee_post_condition = new AndExpression(callee_post_condition, condition);
                                }
                                callee_post_condition.Print(writer);
                                writer.Write("\n");

                                if(stmt.lhs != null){
                                    List<LocalVariable> callee_rtn_vars = stmt.rhs.function.rvs;
                                    if(stmt.lhs.Count != callee_rtn_vars.Count){
                                        // writer.Write("gg2\n");
                                    }
                                    // 形式返回值换成真实返回值
                                    for(int n = 0; n < callee_rtn_vars.Count; n++){
                                        callee_post_condition = callee_post_condition.Substitute(callee_rtn_vars[n], new VariableExpression(stmt.lhs[n]));
                                    }
                                }
                                // 形参换成实参
                                if(stmt.rhs.argumentVariables.Count != stmt.rhs.function.parameters.Count){
                                    // writer.Write("gg5\n");
                                }
                                for(int n = 0; n < stmt.rhs.argumentVariables.Count; n++){
                                    callee_post_condition = callee_post_condition.Substitute(stmt.rhs.function.parameters[n], new VariableExpression(stmt.rhs.argumentVariables[n]));
                                }
                                // assume
                                cur_rank_condition = new ImplicationExpression(callee_post_condition, cur_rank_condition);
                            }
                            else if(cur_statement is AssertStatement){
                                cur_rank_condition = new AndExpression(cur_rank_condition, ((AssertStatement)cur_statement).pred);
                            }
                            else{
                                // writer.Write("gg3\n");
                            }

                            idx -= 1;
                            cur_rank_condition.Print(writer);
                            writer.Write("\n");
                        }

                        // 最终验证条件：pre -> wp[换名]
                        for(int n = 0; n < renamed_variables_list.Count; n++){
                            int cnt = renamed_variables_list[n].Count;
                            for(int m = 0; m < cnt; m++){
                                cur_rank_condition = cur_rank_condition.Substitute(renamed_variables_list[n][m], new VariableExpression(unrenamed_variables_list[n][m]));
                            }
                        }

                        // 将函数头/循环头秩函数非负性加入前置条件
                        Expression strong_pre_condition = pre_condition;
                        foreach(Expression entry_ranking_func in entry_ranking_funcs){
                            strong_pre_condition = new AndExpression(strong_pre_condition, new GEExpression(entry_ranking_func, new IntConstantExpression(0))); 
                        }
                        check_condition = new ImplicationExpression(strong_pre_condition, cur_rank_condition);
                        check_condition.Print(writer);
                        writer.Write("\n");

                        // 对验证条件做验证，如果非有效式，立即返回-1
                        if(solver.CheckValid(check_condition) != null){
                            return -1;
                        }
                    }
                }
            }
            return 1;
        }
    }
}

