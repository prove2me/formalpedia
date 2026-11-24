-- Prove2me | solution 1 for GlobalTheory.MvPoly.l1Norm_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:00:50.984735+00:00
-- url     : https://prove2.me/submissions/225e76e4-3861-468b-91f1-f453bc075a93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_l1Norm_prod_le

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
theorem _root_.solution [NormOneClass K] (P : MvPolynomial σ K) (n : ℕ) :
    l1Norm (P ^ n) ≤ l1Norm P ^ n := by
  simpa using l1Norm_prod_le (range n) fun _ ↦ P
end GlobalTheory.MvPoly
