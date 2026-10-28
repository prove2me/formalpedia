-- Prove2me | solution 1 for IntMul.HvdH.NumL.atanInv_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T05:10:56.721+00:00
-- url     : https://prove2.me/submissions/bbf3ba8f-8ee3-4efa-a429-96432bd8ae1c


import Definitions.Def_IntMul_Kappa_K_Defs33
import Definitions.Def_IntMul_Kappa_R6_Defs1
import Definitions.Def_IntMul_HvdH_Numeric
import Theorems.Thm_IntMul_HvdH_Num_atanInv_bound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open IntMul IntMul.HvdH
open Finset
open IntMul.HvdH


theorem solution (x N K : ℕ) (hx : 2 ≤ x) :
    |(atanInv x N K : ℝ) - 2 ^ N * Real.arctan (1 / x)| ≤ K + 2 * 2 ^ N / x ^ (2 * K + 1) := by
  first
  | exact IntMul.HvdH.Num.atanInv_bound
  | (apply IntMul.HvdH.Num.atanInv_bound <;> assumption)
  | (intros; apply IntMul.HvdH.Num.atanInv_bound <;> assumption)
