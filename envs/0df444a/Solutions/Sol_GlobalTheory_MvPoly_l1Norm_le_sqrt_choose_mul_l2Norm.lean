-- Prove2me | solution 1 for GlobalTheory.MvPoly.l1Norm_le_sqrt_choose_mul_l2Norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:21:17.373799+00:00
-- url     : https://prove2.me/submissions/416a875e-d570-49e5-a3b1-e78e4bdf74ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_card_support_le_choose
import Theorems.Thm_GlobalTheory_MvPoly_l2Norm_nonneg
import Theorems.Thm_GlobalTheory_MvPoly_l1Norm_le_sqrt_card_mul_l2Norm

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
theorem _root_.solution [Fintype σ] {P : MvPolynomial σ K} {d : ℕ}
    (h : P.totalDegree ≤ d) : l1Norm P ≤ √((Fintype.card σ + d).choose d) * l2Norm P :=
  (l1Norm_le_sqrt_card_mul_l2Norm P).trans <| mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (by exact_mod_cast card_support_le_choose h)) (l2Norm_nonneg P)
end GlobalTheory.MvPoly
