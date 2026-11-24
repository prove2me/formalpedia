-- Prove2me | solution 1 for GlobalTheory.RapidFourier.contDiff_wave
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:46.997375+00:00
-- url     : https://prove2.me/submissions/0e1f0c08-af85-4504-85e9-6c179ccaa859

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.RapidFourier
namespace GlobalTheory.RapidFourier
theorem _root_.solution (a : ℂ) : ContDiff ℝ ∞ (wave a) := by
  have h : ContDiff ℝ ∞ fun t : ℝ => ((t : ℝ) : ℂ) := Complex.ofRealCLM.contDiff
  exact contDiff_const.mul ((contDiff_const.mul h).cexp)
end GlobalTheory.RapidFourier
