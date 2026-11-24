-- Prove2me | solution 1 for GlobalTheory.FibLine.eval_hPoly_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:51:30.523814+00:00
-- url     : https://prove2.me/submissions/20c479e9-eadc-4da2-8248-a81c698d3fdf

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
theorem _root_.solution (a : ℂ) (k : ℕ) :
    MvPolynomial.eval ![a + a, a * a] (hPoly k) = ((k : ℂ) + 1) * a ^ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [hPoly_zero]
  | one => simp [hPoly_one]; ring
  | more k h0 h1 =>
    rw [hPoly_add_two]
    simp only [map_sub, map_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [h0, h1]
    push_cast
    ring
end GlobalTheory.FibLine
