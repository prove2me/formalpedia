-- Prove2me | solution 1 for GlobalTheory.MvPoly.l1Norm_le_sqrt_card_mul_l2Norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:00:50.188731+00:00
-- url     : https://prove2.me/submissions/48e34c6c-8bb4-4994-a886-e0f31f05f895

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_sum_le_sqrt_card_mul_sqrt_sum_sq

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
theorem _root_.solution (P : MvPolynomial σ K) :
    l1Norm P ≤ √(#P.support) * l2Norm P :=
  sum_le_sqrt_card_mul_sqrt_sum_sq _ _
end GlobalTheory.MvPoly
