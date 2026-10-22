-- Prove2me | solution 1 for IntMul.HvdH.Num.atanhInv_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T05:14:41.452554+00:00
-- url     : https://prove2.me/submissions/28cf25c6-7d8c-48c6-a8cf-5b969fe03175


import Definitions.Def_IntMul_Kappa_K_Defs33
import Definitions.Def_IntMul_Kappa_R6_Defs1
import Definitions.Def_IntMul_HvdH_Numeric
import Theorems.Thm_IntMul_HvdH_NumL_atanhInv_bound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open IntMul IntMul.HvdH
open Finset
open IntMul.HvdH


theorem solution (x N K : ℕ) (hx : 2 ≤ x) :
    |(atanhInv x N K : ℝ) - 2 ^ N * ((Real.log (1 + 1 / x) - Real.log (1 - 1 / x)) / 2)| ≤ K + 2 * 2 ^ N / x ^ (2 * K + 1) := by
  first
  | exact IntMul.HvdH.NumL.atanhInv_bound
  | (apply IntMul.HvdH.NumL.atanhInv_bound <;> assumption)
  | (intros; apply IntMul.HvdH.NumL.atanhInv_bound <;> assumption)
