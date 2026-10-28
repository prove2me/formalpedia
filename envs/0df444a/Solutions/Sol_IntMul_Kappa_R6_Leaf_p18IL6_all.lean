-- Prove2me | solution 1 for IntMul.Kappa.R6.Leaf.p18IL6_all
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:18:19.258353+00:00
-- url     : https://prove2.me/submissions/d770cf67-6fcd-4b65-ab0e-65eab9c83955

import Definitions.Def_IntMul_Kappa_R6_Defs16
import Theorems.Thm_NLogN_KFV_R6P_p18Body6_of

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R6
open NLogN

/-- `P18IL6` follows from the published Prop. 18 body constructor: under `EwOK6` and
`IL3.P14UH'`, `NLogN.KFV.R6P.p18Body6_of` supplies `P18Body6`, and the remaining
`SwapNeedτ` / `RowUCP` / `FineU6` hypotheses of `P18IL6` are unused by that constructor. -/
theorem solution (P : Prm) (hP : P.Ok) : P18IL6 P :=
  fun tab Ew hEw hU _ _ _ => NLogN.KFV.R6P.p18Body6_of P hP tab Ew hEw hU
