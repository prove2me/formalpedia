-- Prove2me | solution 1 for LinearSetReconciliation327.Main.hintDecAtModel_entry_absolute_problem
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-22T08:51:46.577315+00:00
-- url     : https://prove2.me/submissions/023f0c09-71bf-4c73-a9a2-1b77f40953b9

import Definitions.Def_LinearSetReconciliation327_Main_HintDecAtModel20261122
set_option autoImplicit false
open LinearSetReconciliation327.Main

theorem solution
    (body : Stmt) (G : Program) (base : ℕ) (E : RAMEnv) (s : RAMState)
    (hAt : At G base ((hintDecAtModel body).compile base))
    (hpc : s.pc = base) (hW : 3 < 2 ^ E.W) :
    ((step G E)^[hintDecPre.length + 2] s).regs 6 = E.det 3 % 2 ^ E.W :=
  hintDecAtModel_entry_absolute body G base E s hAt hpc hW
