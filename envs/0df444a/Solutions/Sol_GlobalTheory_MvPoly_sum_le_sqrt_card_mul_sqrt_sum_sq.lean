-- Prove2me | solution 1 for GlobalTheory.MvPoly.sum_le_sqrt_card_mul_sqrt_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:45.857154+00:00
-- url     : https://prove2.me/submissions/d51eaf90-61d8-4252-931c-257e85f31dd1

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, f i ≤ √(#s) * √(∑ i ∈ s, f i ^ 2) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.le_sqrt_of_sq_le sq_sum_le_card_mul_sum_sq
end GlobalTheory.MvPoly
