-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.comm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:05:28.15736+00:00
-- url     : https://prove2.me/submissions/888240db-f58f-4233-b2fd-070dfe52c84a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (ψ : 𝓢(E, ℂ)) (u : 𝓢'(E, ℂ)) :
    comm T ψ u = T (smulLeftCLM ℂ (ψ : E → ℂ) u) - smulLeftCLM ℂ (ψ : E → ℂ) (T u) := rfl
end GroundTheory.Automorphic.Sobolev
