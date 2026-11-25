-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sob_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:55:19.256416+00:00
-- url     : https://prove2.me/submissions/2b677e5e-95c2-4190-b5cd-66eefd9ff0ab

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication

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
theorem _root_.solution {s : ℝ} {u : 𝓢'(E, ℂ)} (h : MemSobolev s 2 u) :
    sob s u = ‖(SobolevSpace.mk u h : SobolevSpace E ℂ s)‖ₑ := by rw [sob, dif_pos h]
end GroundTheory.Automorphic.Sobolev
