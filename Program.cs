using Google.OrTools.Sat;
using Google.OrTools.Util;

Solving_Discrete_Bins();

//Solving_Continous_Bin();

Solving_Better_Continous_Bin();

//Solving_Best_Continous_Bin();

//Solving_Too_Better_Continous_Bins();



//----------------------------------------------------------------------------------------------------

//OF is correct but left,right,bottom and top are incorrect.
static void Solving_Discrete_Bins()
{
    //The approach in this algorithm is exactly similar to MIP in EJOR article.
    //Here for 20 items, I create 40 items for fix and rotated and I put constraint on choosing only one of them
    //In this algorithm I use the sizeitotal and ntotal

    //Parameters
    int[] sizeb={10,10}; //W-H
    int[,] sizei={{9 , 5},
                  {2 , 4},
                  {6 ,10},
                  {7 , 5},
                  {3 , 6},
                  {7 ,10},
                  {5 , 1},
                  {5 , 3},
                  {9 , 6},
                  {4 , 2},
                  {7 , 6},
                  {2 , 7},
                  {3 , 8},
                  {10, 4},
                  {5 , 4},
                  {3 ,10},
                  {3 , 8},
                  {8 , 7},
                  {3 , 8},
                  {7 , 8}};
    // int[,] sizei={ {2	,2},
    //                {8	,6},
    //                {2	,10},
    //                {3	,1},
    //                {4	,8},
    //                {10	,3},
    //                {9	,1},
    //                {5	,1},
    //                {3	,6},
    //                {1	,1},
    //                {2	,4},
    //                {2	,9},
    //                {9	,1},
    //                {5	,9},
    //                {7	,4},
    //                {2	,2},
    //                {4	,3},
    //                {7	,9},
    //                {1	,4},
    //                {8	,9},
    //                {3	,4},
    //                {5	,6},
    //                {7	,4},
    //                {4	,10},
    //                {5	,9},
    //                {2	,1},
    //                {1	,7},
    //                {1	,3},
    //                {3	,8},
    //                {4	,4},
    //                {2	,7},
    //                {9	,6},
    //                {2	,2},
    //                {8	,2},
    //                {1	,4},
    //                {6	,10},
    //                {1	,7},
    //                {9	,3},
    //                {5	,9},
    //                {8	,3}};
    
    int n=sizei.GetLength(0);
    int ntotal=2*n;
    int[,] sizeitotal=new int[ntotal,sizei.GetLength(1)];
    for (int i = 0; i < n; i++)
    {
      sizeitotal[i,0]=sizei[i,0];
      sizeitotal[i,1]=sizei[i,1];
      sizeitotal[i+n,0]=sizei[i,1];
      sizeitotal[i+n,1]=sizei[i,0];
    }

    int m=n; //number of the bins
    List<int> di=new List<int>{418,395,276,279,419,305,291,238,283,149,402,330,264,138,253,365,181,259,345,197};
    // List<int> di=new List<int>{158,129,423,284,469,369,292,121,300,225,376,430,473,462,259,235,320,510,423,225,204,170,429,392,180,540,343,532,247,229,112,349,192,194,185,319,293,160,526,462};

    for (int i = 0; i < n; i++)
    {
        di.Add(di[i]);
    }
    int ptimeb=100; //procceissing time of the bin


    //Create Model
    CpModel model=new CpModel();

    //Variables

    BoolVar[,] f=new BoolVar[ntotal,m];
    for (int i = 0; i < ntotal; i++)
    {
        for (int j = 0; j < m; j++)
        {
            //f[i,j]=1 if item i assign to bin j
            f[i,j]=model.NewBoolVar($"f[{i},{j}]");
        }
    }


    //Constraints
    //Only fixed or rotated can be assigned
    for (int i = 0; i < n; i++)
    {
        List<ILiteral> literals=new List<ILiteral>();
        for (int j = 0; j < m; j++)
        {
            literals.Add(f[i,j]);
            literals.Add(f[i+n,j]);
        }
        model.AddExactlyOne(literals);
    }

    //NoOverlap2D
    IntVar[] left=new IntVar[ntotal];
    IntVar[] right=new IntVar[ntotal];
    IntVar[] bottom=new IntVar[ntotal];
    IntVar[] top=new IntVar[ntotal];

    IntervalVar[] width_iv=new IntervalVar[ntotal];
    IntervalVar[] height_iv=new IntervalVar[ntotal];

    //Creating Domain For left[i] and right[i]
    long[][] xdomain_left=new long[ntotal][];
    long[][] xdomain_right=new long[ntotal][];
   
    long[][] ydomain_bottom=new long[ntotal][];
    long[][] ydomain_top=new long[ntotal][];

    long[] temp_left=new long[sizeb[0]];
    long[] temp_right=new long[sizeb[0]];
   
    long[] possible_x=new long[sizeb[0]+1];
    long[] possible_y=new long[sizeb[1]+1];
    for (int i = 0; i < possible_x.Count(); i++)
    {
        possible_x[i]=i;
    }
    for (int i = 0; i < possible_y.Count(); i++)
    {
        possible_y[i]=i;
    }
    for (int i = 0; i < ntotal; i++)
    {
        xdomain_left[i]=new long[]{};
        xdomain_right[i]=new long[]{};
        xdomain_left[i]=possible_x.Take(sizeb[0]-sizeitotal[i,0]+1).ToArray();
        xdomain_right[i]=possible_x.Skip(sizeitotal[i,0]).ToArray();

        ydomain_bottom[i]=new long[]{};
        ydomain_top[i]=new long[]{};
        ydomain_bottom[i]=possible_y.Take(sizeb[1]-sizeitotal[i,1]+1).ToArray();
        ydomain_top[i]=possible_y.Skip(sizeitotal[i,1]).ToArray();
    }
    
    for (int j = 0; j < m; j++)
    {
        NoOverlap2dConstraint clap=model.AddNoOverlap2D();

        CumulativeConstraint cumulx=model.AddCumulative(sizeb[1]);
        CumulativeConstraint cumuly=model.AddCumulative(sizeb[0]);

        for (int i = 0; i < ntotal; i++)
        {
            //left[i]=model.NewIntVar(0,sizeb[0]-sizeitotal[i,0],$"left{i}");
            left[i]=model.NewIntVarFromDomain(Domain.FromValues(xdomain_left[i]),$"left[{i}]");
            //right[i]=model.NewIntVar(sizeitotal[i,0],sizeb[0],$"right{i}");
            right[i]=model.NewIntVarFromDomain(Domain.FromValues(xdomain_right[i]),$"right[{i}]");

            model.Add(left[i]+sizeitotal[i,0]==right[i]);

            //bottom[i]=model.NewIntVar(0,sizeb[1]-sizeitotal[i,1],$"bottom{i}");
            bottom[i]=model.NewIntVarFromDomain(Domain.FromValues(ydomain_bottom[i]),$"bottom[{i}]");

            //top[i]=model.NewIntVar(sizeitotal[i,1],sizeb[1],$"top{i}");
            top[i]=model.NewIntVarFromDomain(Domain.FromValues(ydomain_top[i]),$"top[{i}]");

            model.Add(bottom[i]+sizeitotal[i,1]==top[i]);

            //width_iv[i]=model.NewIntervalVar(left[i],sizeitotal[i,0],right[i],$"width_iv[{i}]");
            //height_iv[i]=model.NewIntervalVar(bottom[i],sizeitotal[i,1],top[i],$"height_iv[{i}]");
            
            width_iv[i]=model.NewOptionalIntervalVar(left[i],sizeitotal[i,0],right[i],f[i,j],$"width_iv[{i}]");
            height_iv[i]=model.NewOptionalIntervalVar(bottom[i],sizeitotal[i,1],top[i],f[i,j],$"height_iv[{i}]");

            model.Add(left[i]>=0);
            model.Add(bottom[i]>=0);
            model.Add(right[i]<=sizeb[0]);
            model.Add(top[i]<=sizeb[1]);

            
    
            clap.AddRectangle(width_iv[i],height_iv[i]); 

            cumulx.AddDemand(width_iv[i],sizeitotal[i,1]);
            cumuly.AddDemand(height_iv[i],sizeitotal[i,0]);
        }

        
    }


    //Objective Function
    IntVar lmax=model.NewIntVar(ptimeb-di.Max()-1,(n*ptimeb)-di.Min()+1,"lmax");
    IntVar[] l=new IntVar[n];
    for (int i = 0; i < n; i++)
    {
        l[i]=model.NewIntVar(ptimeb-di.Max()-1,(n*ptimeb)-di.Min()+1,$"l[{i}]");
        for (int j = 0; j < m; j++)
        {
            model.Add(l[i]==((j+1)*ptimeb)-di[i]).OnlyEnforceIf(f[i,j]);
            model.Add(l[i]==((j+1)*ptimeb)-di[i]).OnlyEnforceIf(f[i+n,j]);
        }
    }

    model.AddMaxEquality(lmax,l);
    model.Minimize(lmax);



    //Solve
    CpSolver solver=new CpSolver();
    solver.StringParameters="log_search_progress : true, num_search_workers:1";
    CpSolverStatus status=solver.Solve(model);
    System.Console.WriteLine(status);

    if (status==CpSolverStatus.Optimal || status==CpSolverStatus.Feasible)
    {
        for (int j = 0; j < m; j++)
        {
            for (int i = 0; i < ntotal; i++)
            {
                if (solver.Value(f[i,j])==1)
                {
                    System.Console.WriteLine($"Bin[{j}]");
                    System.Console.WriteLine($"f[{i},{j}]={solver.Value(f[i,j])}");
                    System.Console.WriteLine($"left[{i}]={solver.Value(left[i])}---right[{i}]={solver.Value(right[i])}");
                    System.Console.WriteLine($"bottom[{i}]={solver.Value(bottom[i])}---top[{i}]={solver.Value(top[i])}");
                    System.Console.WriteLine("");

                }
                // if (solver.Value(f[i+n,j])==1)
                // {
                //     System.Console.WriteLine($"Bin[{j}]");
                //     System.Console.WriteLine($"f[{i},{j}]Rotated={solver.Value(f[i+n,j])}");
                //     System.Console.WriteLine($"left[{i}]={solver.Value(left[i+n])}---right[{i}]={solver.Value(right[i+n])}");
                //     System.Console.WriteLine($"bottom[{i}]={solver.Value(bottom[i+n])}---top[{i}]={solver.Value(top[i+n])}");
                //     System.Console.WriteLine("");
                    
                // }
            }
            //System.Console.WriteLine("");
        }
        for (int i = 0; i < n; i++)
        {
            System.Console.WriteLine($"l[{i}]={solver.Value(l[i])}");
        }
        System.Console.WriteLine("Objective Function="+solver.ObjectiveValue);
        System.Console.WriteLine("Wall Time ="+solver.WallTime());
    }
    else
    {
        System.Console.WriteLine("No Solution Found!!!!");
    }

}




//----------------------------------------------------------------------------------------------------------
/*
//defined x[i] and left[i] as a coefficient of x[i]
static void Solving_Continous_Bin()
{
    //Parameters
    int[] sizeb={10,10}; //W-H
    int[,] sizei={{9 , 5},
                  {2 , 4},
                  {6 ,10},
                  {7 , 5},
                  {3 , 6},
                  {7 ,10},
                  {5 , 1},
                  {5 , 3},
                  {9 , 6},
                  {4 , 2},
                  {7 , 6},
                  {2 , 7},
                  {3 , 8},
                  {10, 4},
                  {5 , 4},
                  {3 ,10},
                  {3 , 8},
                  {8 , 7},
                  {3 , 8},
                  {7 , 8}};
    
    int n=sizei.GetLength(0);
    int ntotal=2*n;
    // int[,] sizeitotal=new int[ntotal,sizei.GetLength(1)];
    // for (int i = 0; i < n; i++)
    // {
    //   sizeitotal[i,0]=sizei[i,0];
    //   sizeitotal[i,1]=sizei[i,1];
    //   sizeitotal[i+n,0]=sizei[i,1];
    //   sizeitotal[i+n,1]=sizei[i,0];
    // }

    int m=n; //number of the bins
    //int [] di={418,395,276,279,419,305,291,238,283,149,402,330,264,138,253,365,181,259,345,197};
    List<int> di=new List<int>{418,395,276,279,419,305,291,238,283,149,402,330,264,138,253,365,181,259,345,197};
    //int [] ditotal=new int[ntotal];
    for (int i = 0; i < n; i++)
    {
        // ditotal[i]=di[i];
        // ditotal[i+n]=di[i];
        di.Add(di[i]);
    }
    int ptimeb=100; //procceissing time of the bin


    //Create Model
    CpModel model=new CpModel();

    //Variables
    IntVar[] b=new IntVar[n];//number of bins that item i assigned
    BoolVar[] flag=new BoolVar[n];//flag=0 means fixed, flag=1 means rotated
    for (int i = 0; i < n; i++)
    {
        b[i]=model.NewIntVar(0,m-1,$"b[{i}]");
        flag[i]=model.NewBoolVar($"flag[{i}]");
    }


    //NoOverlap2D
    IntVar[] left=new IntVar[n];
    IntVar[] right=new IntVar[n];
    IntVar[] bottom=new IntVar[n];
    IntVar[] top=new IntVar[n];
    IntVar[] x=new IntVar[n];

    IntervalVar[] width_iv=new IntervalVar[n];
    IntervalVar[] height_iv=new IntervalVar[n];

    IntervalVar[] width_iv_II=new IntervalVar[n];
    IntervalVar[] height_iv_II=new IntervalVar[n];
    
    
    NoOverlap2dConstraint clap=model.AddNoOverlap2D();
    for (int i = 0; i < n; i++)
    {
        x[i]=model.NewIntVar(0,sizeb[0]-Math.Min(sizei[i,0],sizei[i,1]),$"x[{i}]");

        left[i]=model.NewIntVar(0,m*sizeb[0]-Math.Min(sizei[i,0],sizei[i,1]),$"left{i}");
        right[i]=model.NewIntVar(Math.Min(sizei[i,0],sizei[i,1]),m*sizeb[0],$"right{i}");
        model.Add(left[i]+sizei[i,0]==right[i]).OnlyEnforceIf(flag[i].Not());
        model.Add(left[i]+sizei[i,1]==right[i]).OnlyEnforceIf(flag[i]);
        model.Add(left[i]==x[i]+(b[i]*sizeb[0]));
        model.Add(right[i]<=(b[i]+1)*sizeb[0]);

        bottom[i]=model.NewIntVar(0,sizeb[1]-Math.Min(sizei[i,1],sizei[i,0]),$"bottom{i}");
        top[i]=model.NewIntVar(Math.Min(sizei[i,1],sizei[i,0]),sizeb[1],$"top{i}");
        model.Add(bottom[i]+sizei[i,1]==top[i]).OnlyEnforceIf(flag[i].Not());
        model.Add(bottom[i]+sizei[i,0]==top[i]).OnlyEnforceIf(flag[i]);


        // width_iv[i]=model.NewIntervalVar(left[i],sizeitotal[i,0],right[i],$"width_iv[{i}]");
        // height_iv[i]=model.NewIntervalVar(bottom[i],sizeitotal[i,1],top[i],$"height_iv[{i}]");
        
        width_iv[i]=model.NewOptionalIntervalVar(left[i],sizei[i,0],right[i],flag[i].Not(),$"width_iv[{i}]");
        height_iv[i]=model.NewOptionalIntervalVar(bottom[i],sizei[i,1],top[i],flag[i].Not(),$"height_iv[{i}]");

        width_iv_II[i]=model.NewOptionalIntervalVar(left[i],sizei[i,1],right[i],flag[i],$"width_iv[{i}]");
        height_iv_II[i]=model.NewOptionalIntervalVar(bottom[i],sizei[i,0],top[i],flag[i],$"height_iv[{i}]");


        model.Add(left[i]>=0);
        model.Add(bottom[i]>=0);
        model.Add(right[i]<=m*sizeb[0]);
        model.Add(top[i]<=sizeb[1]);
        

        clap.AddRectangle(width_iv[i],height_iv[i]);           
        clap.AddRectangle(width_iv_II[i],height_iv_II[i]);           
    }

    //Objective Function
    IntVar lmax=model.NewIntVar(ptimeb-di.Max()-1,(n*ptimeb)-di.Min()+1,"lmax");
    IntVar[] l=new IntVar[n];
    for (int i = 0; i < n; i++)
    {
        l[i]=model.NewIntVar(ptimeb-di.Max()-1,(n*ptimeb)-di.Min()+1,$"l[{i}]");
        
        model.Add(l[i]==((b[i]+1)*ptimeb)-di[i]);
        
    }
    model.AddMaxEquality(lmax,l);
    model.Minimize(lmax);

    //Solve
    CpSolver solver=new CpSolver();
    solver.StringParameters="log_search_progress : true, num_search_workers:1";
    CpSolverStatus status=solver.Solve(model);
    System.Console.WriteLine(status);

    if (status==CpSolverStatus.Optimal || status==CpSolverStatus.Feasible)
    {
        
        for (int i = 0; i < n; i++)
        {
            System.Console.WriteLine($"item[{i}]");
            System.Console.WriteLine($"b[{i}]={solver.Value(b[i])}---flag[{i}]={solver.Value(flag[i])}");
            System.Console.WriteLine($"left[{i}]={solver.Value(left[i])}-right[{i}]={solver.Value(right[i])}");
            System.Console.WriteLine($"bottom[{i}]={solver.Value(bottom[i])}-top[{i}]={solver.Value(top[i])}");
        }
        
        for (int i = 0; i < n; i++)
        {
            System.Console.WriteLine($"l[{i}]={solver.Value(l[i])}");
        }
        System.Console.WriteLine("Objective Function="+solver.ObjectiveValue);
        System.Console.WriteLine("Wall Time ="+solver.WallTime());
    }
    else
    {
        System.Console.WriteLine("No Solution Found!!!!");
    }

}
*/



//--------------------------------------------------------------------------------------------------

static void Solving_Better_Continous_Bin()
{
    //Parameters
    int[] sizeb={10,10}; //W-H
    int[,] sizei={{9 , 5},
                  {2 , 4},
                  {6 ,10},
                  {7 , 5},
                  {3 , 6},
                  {7 ,10},
                  {5 , 1},
                  {5 , 3},
                  {9 , 6},
                  {4 , 2},
                  {7 , 6},
                  {2 , 7},
                  {3 , 8},
                  {10, 4},
                  {5 , 4},
                  {3 ,10},
                  {3 , 8},
                  {8 , 7},
                  {3 , 8},
                  {7 , 8}};
    // int[,] sizei={ {2	,2},
    //                {8	,6},
    //                {2	,10},
    //                {3	,1},
    //                {4	,8},
    //                {10	,3},
    //                {9	,1},
    //                {5	,1},
    //                {3	,6},
    //                {1	,1},
    //                {2	,4},
    //                {2	,9},
    //                {9	,1},
    //                {5	,9},
    //                {7	,4},
    //                {2	,2},
    //                {4	,3},
    //                {7	,9},
    //                {1	,4},
    //                {8	,9},
    //                {3	,4},
    //                {5	,6},
    //                {7	,4},
    //                {4	,10},
    //                {5	,9},
    //                {2	,1},
    //                {1	,7},
    //                {1	,3},
    //                {3	,8},
    //                {4	,4},
    //                {2	,7},
    //                {9	,6},
    //                {2	,2},
    //                {8	,2},
    //                {1	,4},
    //                {6	,10},
    //                {1	,7},
    //                {9	,3},
    //                {5	,9},
    //                {8	,3}};    
    int n=sizei.GetLength(0);
    int ntotal=2*n;

    int m=n; //number of the bins
    //di[i] is the due date of item i
    List<int> di=new List<int>{418,395,276,279,419,305,291,238,283,149,402,330,264,138,253,365,181,259,345,197};
    // List<int> di=new List<int>{158,129,423,284,469,369,292,121,300,225,376,430,473,462,259,235,320,510,423,225,204,170,429,392,180,540,343,532,247,229,112,349,192,194,185,319,293,160,526,462};
    
    int ptimeb=100; //procceissing time of the bin


    //Create Model
    CpModel model=new CpModel();

    //Variables
    BoolVar[] flag=new BoolVar[n];
    for (int i = 0; i < n; i++)
    {
        //flag[i]=0 means fixed item, flag[i]=1 means rotated item
        flag[i]=model.NewBoolVar($"flag[{i}]");
    }

    //Integer Variables for coordinations of items
    IntVar[] left=new IntVar[n];
    IntVar[] right=new IntVar[n];
    IntVar[] bottom=new IntVar[n];
    IntVar[] top=new IntVar[n];
    // IntVar[] left_fix=new IntVar[n];
    // IntVar[] left_rot=new IntVar[n];

    //Interval Variables for fixed items
    IntervalVar[] width_iv=new IntervalVar[n];
    IntervalVar[] height_iv=new IntervalVar[n];
    //Interval Variables for rotated items
    IntervalVar[] width_iv_II=new IntervalVar[n];
    IntervalVar[] height_iv_II=new IntervalVar[n];
    
    //Creating Domain For left[i] and right[i]
    long[][] xdomain_left_fix=new long[n][];
    long[][] xdomain_right_fix=new long[n][];
    long[][] xdomain_left_rot=new long[n][];
    long[][] xdomain_right_rot=new long[n][];

    long[][] ydomain_bottom_fix=new long[n][];
    long[][] ydomain_bottom_rot=new long[n][];
    long[][] ydomain_top_fix=new long[n][];
    long[][] ydomain_top_rot=new long[n][];

    long[] temp_left=new long[sizeb[0]];
    long[] temp_right=new long[sizeb[0]];
    // long[] temp_bottom=new long[sizeb[1]];
    // long[] temp_top=new long[sizeb[1]];
    long[] possible_x=new long[m*sizeb[0]+1];
    long[] possible_y=new long[sizeb[1]+1];
    for (int i = 0; i < possible_x.Count(); i++)
    {
        possible_x[i]=i;
    }
    for (int i = 0; i < possible_y.Count(); i++)
    {
        possible_y[i]=i;
    }
    for (int i = 0; i < n; i++)
    {
        ydomain_bottom_fix[i]=new long[]{};
        ydomain_top_fix[i]=new long[]{};
        ydomain_bottom_fix[i]=possible_y.Take(sizeb[1]-sizei[i,1]+1).ToArray();
        ydomain_top_fix[i]=possible_y.Skip(sizei[i,1]).ToArray();

        xdomain_left_fix[i]=new long[]{};
        xdomain_right_fix[i]=new long[]{};
        for (int j = 0; j < m; j++)
        {
            temp_left=possible_x.Skip(j*sizeb[0]).Take(sizeb[0]-sizei[i,0]+1).ToArray();
            xdomain_left_fix[i]=xdomain_left_fix[i].Concat(temp_left).ToArray();

            temp_right=possible_x.Skip((j*sizeb[0])+sizei[i,0]).Take(sizeb[0]-sizei[i,0]+1).ToArray();
            xdomain_right_fix[i]=xdomain_right_fix[i].Concat(temp_right).ToArray();
        }
    }
    for (int i = 0; i < n; i++)
    {
        ydomain_bottom_rot[i]=new long[]{};
        ydomain_top_rot[i]=new long[]{};
        ydomain_bottom_rot[i]=possible_y.Take(sizeb[1]-sizei[i,0]+1).ToArray();
        ydomain_top_rot[i]=possible_y.Skip(sizei[i,0]).ToArray();

        xdomain_left_rot[i]=new long[]{};
        xdomain_right_rot[i]=new long[]{};
        for (int j = 0; j < m; j++)
        {
            temp_left=possible_x.Skip(j*sizeb[0]).Take(sizeb[0]-sizei[i,1]+1).ToArray();
            xdomain_left_rot[i]=xdomain_left_rot[i].Concat(temp_left).ToArray();

            temp_right=possible_x.Skip((j*sizeb[0])+sizei[i,1]).Take(sizeb[0]-sizei[i,1]+1).ToArray();
            xdomain_right_rot[i]=xdomain_right_rot[i].Concat(temp_right).ToArray();
        }
    }
       

    //Nooverlap2D
    NoOverlap2dConstraint clap=model.AddNoOverlap2D();

    CumulativeConstraint cumulx=model.AddCumulative(sizeb[1]);
    CumulativeConstraint cumuly=model.AddCumulative(m*sizeb[0]);
    for (int i = 0; i < n; i++)
    {
        //left[i]=model.NewIntVar(0,(m*sizeb[0])-Math.Min(sizei[i,0],sizei[i,1]),$"left[{i}]");
        left[i]=model.NewIntVar(0,m*sizeb[0],$"left[{i}]");
        //right[i]=model.NewIntVar(Math.Min(sizei[i,0],sizei[i,1]),m*sizeb[0],$"right[{i}]");
        right[i]=model.NewIntVar(0,m*sizeb[0],$"right[{i}]");

        model.AddLinearExpressionInDomain(LinearExpr.Term(left[i],1),Domain.FromValues(xdomain_left_fix[i])).OnlyEnforceIf(flag[i].Not());
        model.AddLinearExpressionInDomain(LinearExpr.Term(left[i],1),Domain.FromValues(xdomain_left_rot[i])).OnlyEnforceIf(flag[i]);

        // model.AddLinearExpressionInDomain(LinearExpr.Term(right[i],1),Domain.FromValues(xdomain_right_fix[i])).OnlyEnforceIf(flag[i].Not());
        // model.AddLinearExpressionInDomain(LinearExpr.Term(right[i],1),Domain.FromValues(xdomain_right_rot[i])).OnlyEnforceIf(flag[i]);
        
        
        // left_fix[i]=model.NewIntVarFromDomain(Domain.FromValues(xdomain_left_fix[i]),$"left_fix[{i}]");
        // left_rot[i]=model.NewIntVarFromDomain(Domain.FromValues(xdomain_left_rot[i]),$"left_rot[{i}]");


        // model.Add(left[i]==left_fix[i]).OnlyEnforceIf(flag[i].Not());
        // model.Add(left[i]==left_rot[i]).OnlyEnforceIf(flag[i]);

        model.Add(left[i]+sizei[i,0]==right[i]).OnlyEnforceIf(flag[i].Not());
        model.Add(left[i]+sizei[i,1]==right[i]).OnlyEnforceIf(flag[i]);

        bottom[i]=model.NewIntVar(0,sizeb[1],$"bottom{i}");
        top[i]=model.NewIntVar(0,sizeb[1],$"top{i}");

        model.AddLinearExpressionInDomain(LinearExpr.Term(bottom[i],1),Domain.FromValues(ydomain_bottom_fix[i])).OnlyEnforceIf(flag[i].Not());
        model.AddLinearExpressionInDomain(LinearExpr.Term(bottom[i],1),Domain.FromValues(ydomain_bottom_rot[i])).OnlyEnforceIf(flag[i]);

        // model.AddLinearExpressionInDomain(LinearExpr.Term(top[i],1),Domain.FromValues(ydomain_top_fix[i])).OnlyEnforceIf(flag[i].Not());
        // model.AddLinearExpressionInDomain(LinearExpr.Term(top[i],1),Domain.FromValues(ydomain_top_rot[i])).OnlyEnforceIf(flag[i]);

        model.Add(bottom[i]+sizei[i,1]==top[i]).OnlyEnforceIf(flag[i].Not());
        model.Add(bottom[i]+sizei[i,0]==top[i]).OnlyEnforceIf(flag[i]);
        
        width_iv[i]=model.NewOptionalIntervalVar(left[i],sizei[i,0],right[i],flag[i].Not(),$"width_iv[{i}]");
        height_iv[i]=model.NewOptionalIntervalVar(bottom[i],sizei[i,1],top[i],flag[i].Not(),$"height_iv[{i}]");

        width_iv_II[i]=model.NewOptionalIntervalVar(left[i],sizei[i,1],right[i],flag[i],$"width_iv[{i}]");
        height_iv_II[i]=model.NewOptionalIntervalVar(bottom[i],sizei[i,0],top[i],flag[i],$"height_iv[{i}]");


        model.Add(left[i]>=0);
        model.Add(bottom[i]>=0);
        model.Add(right[i]<=m*sizeb[0]);
        model.Add(top[i]<=sizeb[1]);
        

        clap.AddRectangle(width_iv[i],height_iv[i]);           
        clap.AddRectangle(width_iv_II[i],height_iv_II[i]);
       
        cumulx.AddDemand(width_iv[i],sizei[i,1]);
        cumulx.AddDemand(width_iv_II[i],sizei[i,0]); 
        cumuly.AddDemand(height_iv[i],sizei[i,0]);
        cumuly.AddDemand(height_iv_II[i],sizei[i,1]);

    }

    //Objective Function
    IntVar lmax=model.NewIntVar(ptimeb-di.Max()-1,(n*ptimeb)-di.Min()+1,"lmax");
    IntVar[] l=new IntVar[n];
    IntVar[] b=new IntVar[n];
    for (int i = 0; i < n; i++)
    {
        b[i]=model.NewIntVar(0,m,$"b[{i}]");
        l[i]=model.NewIntVar(ptimeb-di.Max()-1,(n*ptimeb)-di.Min()+1,$"l[{i}]");
        model.AddDivisionEquality(b[i],left[i],sizeb[0]);
        // model.AddDivisionEquality(b[i],right[i]-1,sizeb[0]);
        model.Add(l[i]==((b[i]+1)*ptimeb)-di[i]);
        
    }
    model.AddMaxEquality(lmax,l);
    model.Minimize(lmax);

    //Solve
    CpSolver solver=new CpSolver();
    solver.StringParameters="log_search_progress : true, num_search_workers:1";
    // solver.StringParameters="max_time_in_seconds:10.0";
    CpSolverStatus status=solver.Solve(model);
    System.Console.WriteLine(status);

    if (status==CpSolverStatus.Optimal || status==CpSolverStatus.Feasible)
    {
        
        for (int i = 0; i < n; i++)
        {
            System.Console.WriteLine($"[{i}]");
            System.Console.WriteLine($"b[{i}]={solver.Value(b[i])}---flag[{i}]={solver.Value(flag[i])}");
            System.Console.WriteLine($"left[{i}]={solver.Value(left[i])}-right[{i}]={solver.Value(right[i])}");
            System.Console.WriteLine($"bottom[{i}]={solver.Value(bottom[i])}-top[{i}]={solver.Value(top[i])}");
            System.Console.WriteLine("");
        }
        
        for (int i = 0; i < n; i++)
        {
            System.Console.WriteLine($"l[{i}]={solver.Value(l[i])}");
        }
        System.Console.WriteLine("Objective Function="+solver.ObjectiveValue);
        System.Console.WriteLine("Wall Time ="+solver.WallTime());
    }
    else
    {
        System.Console.WriteLine("No Solution Found!!!!");
    }

}





//------------------------------------------------------------------------------------------------------
/*
static void Solving_Best_Continous_Bin()
{
    //Parameters
    int[] sizeb={10,10}; //W-H
    int[,] sizei={{9 , 5},
                  {2 , 4},
                  {6 ,10},
                  {7 , 5},
                  {3 , 6},
                  {7 ,10},
                  {5 , 1},
                  {5 , 3},
                  {9 , 6},
                  {4 , 2},
                  {7 , 6},
                  {2 , 7},
                  {3 , 8},
                  {10, 4},
                  {5 , 4},
                  {3 ,10},
                  {3 , 8},
                  {8 , 7},
                  {3 , 8},
                  {7 , 8}};
    // int[,] sizei={ {2	,2},
    //                {8	,6},
    //                {2	,10},
    //                {3	,1},
    //                {4	,8},
    //                {10	,3},
    //                {9	,1},
    //                {5	,1},
    //                {3	,6},
    //                {1	,1},
    //                {2	,4},
    //                {2	,9},
    //                {9	,1},
    //                {5	,9},
    //                {7	,4},
    //                {2	,2},
    //                {4	,3},
    //                {7	,9},
    //                {1	,4},
    //                {8	,9},
    //                {3	,4},
    //                {5	,6},
    //                {7	,4},
    //                {4	,10},
    //                {5	,9},
    //                {2	,1},
    //                {1	,7},
    //                {1	,3},
    //                {3	,8},
    //                {4	,4},
    //                {2	,7},
    //                {9	,6},
    //                {2	,2},
    //                {8	,2},
    //                {1	,4},
    //                {6	,10},
    //                {1	,7},
    //                {9	,3},
    //                {5	,9},
    //                {8	,3}};    
    int n=sizei.GetLength(0);
    int ntotal=2*n;

    int m=n; //number of the bins
    List<int> di=new List<int>{418,395,276,279,419,305,291,238,283,149,402,330,264,138,253,365,181,259,345,197};
    // List<int> di=new List<int>{158,129,423,284,469,369,292,121,300,225,376,430,473,462,259,235,320,510,423,225,204,170,429,392,180,540,343,532,247,229,112,349,192,194,185,319,293,160,526,462};
    int ptimeb=100; //procceissing time of the bin


    //Create Model
    CpModel model=new CpModel();

    //Variables
    BoolVar[] flag=new BoolVar[n];//flag=0 means fixed, flag=1 means rotated
    for (int i = 0; i < n; i++)
    {
        flag[i]=model.NewBoolVar($"flag[{i}]");
    }

    //NoOverlap2D
    IntVar[] left=new IntVar[n];
    // IntVar[] right=new IntVar[n];
    IntVar[] bottom=new IntVar[n];
    IntVar[] top=new IntVar[n];
    // IntVar[] left_fix=new IntVar[n];
    // IntVar[] left_rot=new IntVar[n];
    IntVar[] right_fix=new IntVar[n];
    IntVar[] right_rot=new IntVar[n];


    IntervalVar[] width_iv=new IntervalVar[n];
    IntervalVar[] height_iv=new IntervalVar[n];

    IntervalVar[] width_iv_II=new IntervalVar[n];
    IntervalVar[] height_iv_II=new IntervalVar[n];
    
    //Creating Domain For left[i] and right[i]
    long[][] xdomain_left_fix=new long[n][];
    long[][] xdomain_right_fix=new long[n][];
    long[][] xdomain_left_rot=new long[n][];
    long[][] xdomain_right_rot=new long[n][];
    long[] temp_left=new long[sizeb[0]];
    long[] temp_right=new long[sizeb[0]];
    long[] possible_x=new long[m*sizeb[0]+1];
    for (int i = 0; i < possible_x.Count(); i++)
    {
        possible_x[i]=i;
    }
    for (int i = 0; i < n; i++)
    {
        xdomain_left_fix[i]=new long[]{};
        xdomain_right_fix[i]=new long[]{};
        for (int j = 0; j < m; j++)
        {
            temp_left=possible_x.Skip(j*sizeb[0]).Take(sizeb[0]-sizei[i,0]+1).ToArray();
            xdomain_left_fix[i]=xdomain_left_fix[i].Concat(temp_left).ToArray();

            temp_right=possible_x.Skip((j*sizeb[0])+sizei[i,0]).Take(sizeb[0]-sizei[i,0]+1).ToArray();
            xdomain_right_fix[i]=xdomain_right_fix[i].Concat(temp_right).ToArray();
        }
    }
    for (int i = 0; i < n; i++)
    {
        xdomain_left_rot[i]=new long[]{};
        xdomain_right_rot[i]=new long[]{};
        for (int j = 0; j < m; j++)
        {
            temp_left=possible_x.Skip(j*sizeb[0]).Take(sizeb[0]-sizei[i,1]+1).ToArray();
            xdomain_left_rot[i]=xdomain_left_rot[i].Concat(temp_left).ToArray();

            temp_right=possible_x.Skip((j*sizeb[0])+sizei[i,1]).Take(sizeb[0]-sizei[i,1]+1).ToArray();
            xdomain_right_rot[i]=xdomain_right_rot[i].Concat(temp_right).ToArray();
        }
    }
    
    NoOverlap2dConstraint clap=model.AddNoOverlap2D();

    // CumulativeConstraint cumulx=model.AddCumulative(sizeb[1]);
    // CumulativeConstraint cumuly=model.AddCumulative(m*sizeb[0]);
    for (int i = 0; i < n; i++)
    {
        
        left[i]=model.NewIntVar(0,(m*sizeb[0])-Math.Min(sizei[i,0],sizei[i,1]),$"left[{i}]");
        // right[i]=model.NewIntVar(Math.Min(sizei[i,0],sizei[i,1]),m*sizeb[0],$"right[{i}]");
        
        // left_fix[i]=model.NewIntVarFromDomain(Domain.FromValues(xdomain_left_fix[i]),$"left_fix[{i}]");
        // left_rot[i]=model.NewIntVarFromDomain(Domain.FromValues(xdomain_left_rot[i]),$"left_rot[{i}]");
        right_fix[i]=model.NewIntVarFromDomain(Domain.FromValues(xdomain_right_fix[i]),$"right_fix[{i}]");
        right_rot[i]=model.NewIntVarFromDomain(Domain.FromValues(xdomain_right_rot[i]),$"left_rot[{i}]");

        // model.Add(left[i]==left_fix[i]).OnlyEnforceIf(flag[i].Not());
        // model.Add(left[i]==left_rot[i]).OnlyEnforceIf(flag[i]);

        model.Add(left[i]+sizei[i,0]==right_fix[i]).OnlyEnforceIf(flag[i].Not());
        model.Add(left[i]+sizei[i,1]==right_rot[i]).OnlyEnforceIf(flag[i]);

        bottom[i]=model.NewIntVar(0,sizeb[1]-Math.Min(sizei[i,1],sizei[i,0]),$"bottom{i}");
        top[i]=model.NewIntVar(Math.Min(sizei[i,1],sizei[i,0]),sizeb[1],$"top{i}");
        model.Add(bottom[i]+sizei[i,1]==top[i]).OnlyEnforceIf(flag[i].Not());
        model.Add(bottom[i]+sizei[i,0]==top[i]).OnlyEnforceIf(flag[i]);
        
        width_iv[i]=model.NewOptionalIntervalVar(left[i],sizei[i,0],right_fix[i],flag[i].Not(),$"width_iv[{i}]");
        height_iv[i]=model.NewOptionalIntervalVar(bottom[i],sizei[i,1],top[i],flag[i].Not(),$"height_iv[{i}]");

        width_iv_II[i]=model.NewOptionalIntervalVar(left[i],sizei[i,1],right_rot[i],flag[i],$"width_iv[{i}]");
        height_iv_II[i]=model.NewOptionalIntervalVar(bottom[i],sizei[i,0],top[i],flag[i],$"height_iv[{i}]");


        model.Add(left[i]>=0);
        model.Add(bottom[i]>=0);
        model.Add(right_fix[i]<=m*sizeb[0]);
        model.Add(right_rot[i]<=m*sizeb[0]);
        model.Add(top[i]<=sizeb[1]);
        

        clap.AddRectangle(width_iv[i],height_iv[i]);           
        clap.AddRectangle(width_iv_II[i],height_iv_II[i]);
       
        // cumulx.AddDemand(width_iv[i],sizei[i,1]);
        // cumulx.AddDemand(width_iv_II[i],sizei[i,0]); 
        // cumuly.AddDemand(height_iv[i],sizei[i,0]);
        // cumuly.AddDemand(height_iv_II[i],sizei[i,1]);

    }

    //Objective Function
    IntVar lmax=model.NewIntVar(ptimeb-di.Max()-1,(n*ptimeb)-di.Min()+1,"lmax");
    IntVar[] l=new IntVar[n];
    IntVar[] b=new IntVar[n];
    for (int i = 0; i < n; i++)
    {
        b[i]=model.NewIntVar(0,m,$"b[{i}]");
        l[i]=model.NewIntVar(ptimeb-di.Max()-1,(n*ptimeb)-di.Min()+1,$"l[{i}]");
        model.AddDivisionEquality(b[i],left[i],sizeb[0]);
        // model.AddDivisionEquality(b[i],right_fix[i]-1,sizeb[0]);
        // model.AddDivisionEquality(b[i],right_rot[i]-1,sizeb[0]);
        model.Add(l[i]==((b[i]+1)*ptimeb)-di[i]);
        
    }
    model.AddMaxEquality(lmax,l);
    model.Minimize(lmax);

    //Solve
    CpSolver solver=new CpSolver();
    solver.StringParameters="log_search_progress : true, num_search_workers:1";
    CpSolverStatus status=solver.Solve(model);
    System.Console.WriteLine(status);

    if (status==CpSolverStatus.Optimal || status==CpSolverStatus.Feasible)
    {
        
        for (int i = 0; i < n; i++)
        {
            System.Console.WriteLine($"[{i}]");
            System.Console.WriteLine($"b[{i}]={solver.Value(b[i])}---flag[{i}]={solver.Value(flag[i])}");
            System.Console.WriteLine($"left_fix[{i}]={solver.Value(left[i])}-right[{i}]={solver.Value(right_fix[i])}");
            System.Console.WriteLine($"left_rot[{i}]={solver.Value(left[i])}-right[{i}]={solver.Value(right_rot[i])}");
            System.Console.WriteLine($"bottom[{i}]={solver.Value(bottom[i])}-top[{i}]={solver.Value(top[i])}");
            System.Console.WriteLine("");
        }
        
        for (int i = 0; i < n; i++)
        {
            System.Console.WriteLine($"l[{i}]={solver.Value(l[i])}");
        }
        System.Console.WriteLine("Objective Function="+solver.ObjectiveValue);
        System.Console.WriteLine("Wall Time ="+solver.WallTime());
    }
    else
    {
        System.Console.WriteLine("No Solution Found!!!!");
    }
}
*/





//-------------------------------------------------------------------------------------------------------
/*
static void Solving_Too_Better_Continous_Bins()
{
    //Parameters
    int[] sizeb={10,10}; //W-H
    int[,] sizei={{9 , 5},
                  {2 , 4},
                  {6 ,10},
                  {7 , 5},
                  {3 , 6},
                  {7 ,10},
                  {5 , 1},
                  {5 , 3},
                  {9 , 6},
                  {4 , 2},
                  {7 , 6},
                  {2 , 7},
                  {3 , 8},
                  {10, 4},
                  {5 , 4},
                  {3 ,10},
                  {3 , 8},
                  {8 , 7},
                  {3 , 8},
                  {7 , 8}};
    // int[,] sizei={ {2	,2},
    //                {8	,6},
    //                {2	,10},
    //                {3	,1},
    //                {4	,8},
    //                {10	,3},
    //                {9	,1},
    //                {5	,1},
    //                {3	,6},
    //                {1	,1},
    //                {2	,4},
    //                {2	,9},
    //                {9	,1},
    //                {5	,9},
    //                {7	,4},
    //                {2	,2},
    //                {4	,3},
    //                {7	,9},
    //                {1	,4},
    //                {8	,9},
    //                {3	,4},
    //                {5	,6},
    //                {7	,4},
    //                {4	,10},
    //                {5	,9},
    //                {2	,1},
    //                {1	,7},
    //                {1	,3},
    //                {3	,8},
    //                {4	,4},
    //                {2	,7},
    //                {9	,6},
    //                {2	,2},
    //                {8	,2},
    //                {1	,4},
    //                {6	,10},
    //                {1	,7},
    //                {9	,3},
    //                {5	,9},
    //                {8	,3}};
    
    int n=sizei.GetLength(0);
    int ntotal=2*n;
    int[,] sizeitotal=new int[ntotal,sizei.GetLength(1)];
    for (int i = 0; i < n; i++)
    {
      sizeitotal[i,0]=sizei[i,0];
      sizeitotal[i,1]=sizei[i,1];
      sizeitotal[i+n,0]=sizei[i,1];
      sizeitotal[i+n,1]=sizei[i,0];
    }

    int m=n; //number of the bins
    List<int> di=new List<int>{418,395,276,279,419,305,291,238,283,149,402,330,264,138,253,365,181,259,345,197};
    // List<int> di=new List<int>{158,129,423,284,469,369,292,121,300,225,376,430,473,462,259,235,320,510,423,225,204,170,429,392,180,540,343,532,247,229,112,349,192,194,185,319,293,160,526,462};

    for (int i = 0; i < n; i++)
    {
        di.Add(di[i]);
    }
    int ptimeb=100; //procceissing time of the bin


    //Create Model
    CpModel model=new CpModel();

    //Variables
    
    BoolVar[] flag=new BoolVar[ntotal];//flag[i]=1 means we consider the item i
    for (int i = 0; i < ntotal; i++)
    {
        flag[i]=model.NewBoolVar($"flag[{i}]");
    }

    //Constraints
    for (int i = 0; i < n; i++)
    {
        List<ILiteral> literals=new List<ILiteral>();
        literals.Add(flag[i]);
        literals.Add(flag[i+n]);
        model.AddExactlyOne(literals);
        // model.Add(flag[i]+flag[i+n]==1);

    }

    //Integer Variables for coordinations of items
    IntVar[] left=new IntVar[ntotal];
    IntVar[] right=new IntVar[ntotal];
    IntVar[] bottom=new IntVar[ntotal];
    IntVar[] top=new IntVar[ntotal];

    IntervalVar[] width_iv=new IntervalVar[ntotal];
    IntervalVar[] height_iv=new IntervalVar[ntotal];
    
    //Creating Domain For left[i] and right[i]
    long[][] xdomain_left=new long[ntotal][];
    long[][] xdomain_right=new long[ntotal][];
   

    long[][] ydomain_bottom=new long[ntotal][];
    long[][] ydomain_top=new long[ntotal][];
    

    long[] temp_left=new long[sizeb[0]];
    long[] temp_right=new long[sizeb[0]];
    
    long[] possible_x=new long[m*sizeb[0]+1];
    long[] possible_y=new long[sizeb[1]+1];
    for (int i = 0; i < possible_x.Count(); i++)
    {
        possible_x[i]=i;
    }
    for (int i = 0; i < possible_y.Count(); i++)
    {
        possible_y[i]=i;
    }
    for (int i = 0; i < ntotal; i++)
    {
        ydomain_bottom[i]=new long[]{};
        ydomain_top[i]=new long[]{};
        ydomain_bottom[i]=possible_y.Take(sizeb[1]-sizeitotal[i,1]+1).ToArray();
        ydomain_top[i]=possible_y.Skip(sizeitotal[i,1]).ToArray();

        xdomain_left[i]=new long[]{};
        xdomain_right[i]=new long[]{};
        for (int j = 0; j < m; j++)
        {
            temp_left=possible_x.Skip(j*sizeb[0]).Take(sizeb[0]-sizeitotal[i,0]+1).ToArray();
            xdomain_left[i]=xdomain_left[i].Concat(temp_left).ToArray();

            temp_right=possible_x.Skip((j*sizeb[0])+sizeitotal[i,0]).Take(sizeb[0]-sizeitotal[i,0]+1).ToArray();
            xdomain_right[i]=xdomain_right[i].Concat(temp_right).ToArray();
        }
    }

    //Nooverlap2D
    NoOverlap2dConstraint clap=model.AddNoOverlap2D();

    CumulativeConstraint cumulx=model.AddCumulative(sizeb[1]);
    CumulativeConstraint cumuly=model.AddCumulative(m*sizeb[0]);
    for (int i = 0; i < ntotal; i++)
    {
        left[i]=model.NewIntVarFromDomain(Domain.FromValues(xdomain_left[i]),$"left[{i}]");
        right[i]=model.NewIntVarFromDomain(Domain.FromValues(xdomain_right[i]),$"right[{i}]");
        
        model.Add(left[i]+sizeitotal[i,0]==right[i]).OnlyEnforceIf(flag[i]);
        model.Add(left[i]==0).OnlyEnforceIf(flag[i].Not());

        bottom[i]=model.NewIntVarFromDomain(Domain.FromValues(ydomain_bottom[i]),$"bottom[{i}]");
        top[i]=model.NewIntVarFromDomain(Domain.FromValues(ydomain_top[i]),$"top[{i}]");

        model.Add(bottom[i]+sizeitotal[i,1]==top[i]).OnlyEnforceIf(flag[i]);
        model.Add(bottom[i]==0).OnlyEnforceIf(flag[i].Not());
        
        width_iv[i]=model.NewOptionalIntervalVar(left[i],sizeitotal[i,0],right[i],flag[i],$"width_iv[{i}]");
        height_iv[i]=model.NewOptionalIntervalVar(bottom[i],sizeitotal[i,1],top[i],flag[i],$"height_iv[{i}]");

        model.Add(left[i]>=0);
        model.Add(bottom[i]>=0);
        model.Add(right[i]<=m*sizeb[0]);
        model.Add(top[i]<=sizeb[1]);
        

        clap.AddRectangle(width_iv[i],height_iv[i]);           
        
       
        cumulx.AddDemand(width_iv[i],sizeitotal[i,1]);
        cumuly.AddDemand(height_iv[i],sizeitotal[i,0]);

    }

    //Objective Function
    IntVar lmax=model.NewIntVar(ptimeb-di.Max()-1,(n*ptimeb)-di.Min()+1,"lmax");
    IntVar[] l=new IntVar[ntotal];
    IntVar[] b=new IntVar[ntotal];
    for (int i = 0; i < ntotal; i++)
    {
        b[i]=model.NewIntVar(0,m,$"b[{i}]");
        l[i]=model.NewIntVar(ptimeb-di.Max()-1,(n*ptimeb)-di.Min()+1,$"l[{i}]");

        model.AddDivisionEquality(b[i],left[i],sizeb[0]);
        model.Add(l[i]==((b[i]+1)*ptimeb)-(di[i])).OnlyEnforceIf(flag[i]);
        // model.Add(l[i]==((b[i])*ptimeb)).OnlyEnforceIf(flag[i].Not());
        
    }
    model.AddMaxEquality(lmax,l);
    model.Minimize(lmax);



    //Solve
    CpSolver solver=new CpSolver();
    solver.StringParameters="log_search_progress : true, num_search_workers:1";
    // solver.StringParameters="max_time_in_seconds:10.0";
    
    CpSolverStatus status=solver.Solve(model);
    System.Console.WriteLine(status);

    if (status==CpSolverStatus.Optimal || status==CpSolverStatus.Feasible)
    {
        
        for (int i = 0; i < ntotal; i++)
        {
            System.Console.WriteLine($"[{i}]");
            System.Console.WriteLine($"b[{i}]={solver.Value(b[i])}---flag[{i}]={solver.Value(flag[i])}");
            System.Console.WriteLine($"left[{i}]={solver.Value(left[i])}-right[{i}]={solver.Value(right[i])}");
            System.Console.WriteLine($"bottom[{i}]={solver.Value(bottom[i])}-top[{i}]={solver.Value(top[i])}");
            System.Console.WriteLine("");
        }
        
        for (int i = 0; i < ntotal; i++)
        {
            System.Console.WriteLine($"l[{i}]={solver.Value(l[i])}");
        }
        System.Console.WriteLine("Objective Function="+solver.ObjectiveValue);
        System.Console.WriteLine("Wall Time ="+solver.WallTime());
    }
    else
    {
        System.Console.WriteLine("No Solution Found!!!!");
    }
   
}
*/



