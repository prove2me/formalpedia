-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sob_toDistribution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:21.342947+00:00
-- url     : https://prove2.me/submissions/ff7ef8d7-2196-4595-a24c-4ca73fd8f43a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_of_mem
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_mk_toDistribution
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_memSobolev_toDistribution


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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (χ : 𝓢(E, ℂ))
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (v : SobolevSpace E ℂ s) :
    sob s (SobolevSpace.toDistribution v) = ‖v‖ₑ := by
  rw [sob_of_mem (SobolevSpace.memSobolev_toDistribution v), mk_toDistribution]
end GroundTheory.Automorphic.Sobolev
