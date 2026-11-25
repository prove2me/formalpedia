-- Prove2me | solution 1 for GlobalTheory.MvPoly.fockNormSq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:05:09.971984+00:00
-- url     : https://prove2.me/submissions/dd675ebd-5048-46f4-b875-2eb13efbf52d

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
theorem _root_.solution (P : MvPolynomial σ K) : 0 ≤ fockNormSq P :=
  sum_nonneg fun _ _ ↦ by positivity
end GlobalTheory.MvPoly
