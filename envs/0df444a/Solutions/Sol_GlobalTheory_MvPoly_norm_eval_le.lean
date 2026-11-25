-- Prove2me | solution 1 for GlobalTheory.MvPoly.norm_eval_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:32.594454+00:00
-- url     : https://prove2.me/submissions/a48555f0-3d0d-4abd-a552-fb1f064bbc47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_norm_eval_le_of_le

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
theorem _root_.solution [NormOneClass K] [Fintype σ] (x : σ → K) (P : MvPolynomial σ K) :
    ‖eval x P‖ ≤ l1Norm P * max 1 ‖x‖ ^ P.totalDegree :=
  norm_eval_le_of_le x P (norm_le_pi_norm x) le_rfl
end GlobalTheory.MvPoly
