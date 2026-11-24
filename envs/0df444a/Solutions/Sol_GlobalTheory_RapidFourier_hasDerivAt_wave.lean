-- Prove2me | solution 1 for GlobalTheory.RapidFourier.hasDerivAt_wave
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:47.19467+00:00
-- url     : https://prove2.me/submissions/f7cc30f7-af1e-47d4-aaa0-7d164da8fcf4

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
theorem _root_.solution (a : ℂ) (t : ℝ) :
    HasDerivAt (wave a) (wave (2 * π * I * a) t) t := by
  have h := (((hasDerivAt_id (t : ℂ)).const_mul (2 * π * I)).cexp.const_mul a).comp_ofReal
  convert h using 1
  · funext y
    simp [wave]
  · simp only [wave, id]
    ring
end GlobalTheory.RapidFourier
