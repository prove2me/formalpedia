-- Prove2me | solution 1 for GlobalTheory.MvPoly.factorial_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:00:46.567975+00:00
-- url     : https://prove2.me/submissions/de1b7568-309d-4a49-8a8f-4cc7bab0cad3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open GlobalTheory GlobalTheory.MvPoly
variable {σ τ K L : Type*}
variable [NormedCommRing K]
namespace GlobalTheory.MvPoly
theorem _root_.solution (i : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (i.factorial : ℝ) * R ^ i ≤ (i * R) ^ i := by
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le_pow i) (pow_nonneg hR _)
end GlobalTheory.MvPoly
