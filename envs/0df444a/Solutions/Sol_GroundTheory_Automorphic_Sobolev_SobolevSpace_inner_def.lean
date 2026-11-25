-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.SobolevSpace.inner_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:59:32.429168+00:00
-- url     : https://prove2.me/submissions/af6a406b-c2ed-4969-8495-99ad9ea5d2ed

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
open GroundTheory.Automorphic.Sobolev.SobolevSpace
variable {s : ℝ}
namespace GroundTheory.Automorphic.Sobolev.SobolevSpace
theorem _root_.solution (u v : SobolevSpace E F s) :
    inner ℂ u v = inner ℂ (bessel s u) (bessel s v) := rfl
end GroundTheory.Automorphic.Sobolev.SobolevSpace
