-- Prove2me | solution 1 for GlobalTheory.MvPoly.sum_norm_coeff_mul_pow_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:02:49.876179+00:00
-- url     : https://prove2.me/submissions/3cf30c07-b7fd-4d60-b474-612e9e8e2764

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
theorem _root_.solution {P : MvPolynomial σ K} {d : ℕ}
    (hP : P.IsHomogeneous d) (R : ℝ) :
    ∑ α ∈ P.support, ‖P.coeff α‖ * R ^ α.degree = l1Norm P * R ^ d := by
  rw [l1Norm, sum_mul]
  refine sum_congr rfl fun α hα ↦ ?_
  rw [hP.degree_eq_sum_deg_support hα, Finsupp.degree_apply]
end GlobalTheory.MvPoly
