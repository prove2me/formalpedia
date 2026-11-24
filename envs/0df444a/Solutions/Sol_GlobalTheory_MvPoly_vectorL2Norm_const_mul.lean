-- Prove2me | solution 1 for GlobalTheory.MvPoly.vectorL2Norm_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:02:51.632104+00:00
-- url     : https://prove2.me/submissions/4124ea41-423b-4b18-9999-1310fd3aba69

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
variable [NormedCommRing K] [NormedCommRing L]
namespace GlobalTheory.MvPoly
theorem _root_.solution [NormMulClass K] (c : K) (P : MvPolynomial σ K) :
    l2Norm (c • P) = ‖c‖ * l2Norm P := by
  rw [l2Norm_eq_sqrt_sum_of_subset (s := P.support) support_smul, l2Norm,
    ← Real.sqrt_sq (norm_nonneg c), ← Real.sqrt_mul (sq_nonneg _), mul_sum]
  simp [mul_pow]
end GlobalTheory.MvPoly
