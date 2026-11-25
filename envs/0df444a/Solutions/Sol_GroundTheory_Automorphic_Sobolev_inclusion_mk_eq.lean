-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.inclusion_mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:12.952799+00:00
-- url     : https://prove2.me/submissions/690459b3-6755-4403-89a9-6519459c1c89

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs

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
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (u : SobolevSpace E F s)
    (hu : MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u)) :
    SobolevSpace.inclusion (le_add_of_nonneg_right zero_le_one) (SobolevSpace.mk (s := s + 1) _ hu) = u := by
  apply SobolevSpace.toDistribution_injective
  rw [SobolevSpace.toDistribution_inclusion, SobolevSpace.toDistribution_mk]
end GroundTheory.Automorphic.Sobolev
