-- Prove2me | solution 1 for GlobalTheory.MvPoly.fockInner_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:06:54.571145+00:00
-- url     : https://prove2.me/submissions/e5e95451-70f7-4954-b398-eac675f44675

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
variable {𝕜 : Type*} [RCLike 𝕜]
namespace GlobalTheory.MvPoly
theorem _root_.solution (P : MvPolynomial σ 𝕜) : fockInner P P = (fockNormSq P : 𝕜) := by
  simp [fockInner, fockNormSq, RCLike.mul_conj]
end GlobalTheory.MvPoly
