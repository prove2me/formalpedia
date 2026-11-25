-- Prove2me | solution 1 for GlobalTheory.MvPoly.l1Norm_linearForm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:16.241979+00:00
-- url     : https://prove2.me/submissions/ed6e9bcd-358d-47d9-bed5-ff78478870f4

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
variable [NormedCommRing K]
namespace GlobalTheory.MvPoly
theorem _root_.solution {ι : Type*} [Fintype ι] (v : ι → σ) (e : ι → K) :
    l1Norm (∑ k, C (e k) * X (v k) : MvPolynomial σ K) ≤
      √(Fintype.card ι) * √(∑ k, ‖e k‖ ^ 2) :=
  (l1Norm_linearForm_le_sum _ v e).trans (sum_le_sqrt_card_mul_sqrt_sum_sq _ _)
end GlobalTheory.MvPoly
