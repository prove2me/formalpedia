-- Prove2me | solution 1 for GlobalTheory.FibLine.sub_mul_eval_hPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:00:40.736807+00:00
-- url     : https://prove2.me/submissions/315b408e-246e-4acd-9027-e1b08cd81ee3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAffinePowEqHPoly
import Theorems.Thm_GlobalTheory_FibLine_hPoly_add_two
import Theorems.Thm_GlobalTheory_FibLine_hPoly_one
import Theorems.Thm_GlobalTheory_FibLine_hPoly_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine
namespace GlobalTheory.FibLine
theorem _root_.solution (a b : ℂ) (k : ℕ) :
    (a - b) * MvPolynomial.eval ![a + b, a * b] (hPoly k) = a ^ (k + 1) - b ^ (k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [hPoly_zero]
  | one => simp [hPoly_one]; ring
  | more k h0 h1 =>
    rw [hPoly_add_two]
    simp only [map_sub, map_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination (a + b) * h1 - (a * b) * h0
end GlobalTheory.FibLine
