-- Prove2me | solution 1 for GlobalTheory.MvPoly.l1Norm_bind_le_mul_pow_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:05:13.826962+00:00
-- url     : https://prove2.me/submissions/651888cd-2eb8-4f14-88ca-6abafe011f0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_l1Norm_bind_le_sum_norm_coeff_mul_pow_degree
import Theorems.Thm_GlobalTheory_MvPoly_sum_norm_coeff_mul_pow_of_isHomogeneous

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
theorem _root_.solution [NormOneClass K] (f : σ → MvPolynomial τ K)
    {P : MvPolynomial σ K} {d : ℕ} (hP : P.IsHomogeneous d) {R : ℝ}
    (h : ∀ i, l1Norm (f i) ≤ R) : l1Norm (bind₁ f P) ≤ l1Norm P * R ^ d :=
  (l1Norm_bind_le_sum_norm_coeff_mul_pow_degree f P h).trans_eq (sum_norm_coeff_mul_pow_of_isHomogeneous hP R)
end GlobalTheory.MvPoly
