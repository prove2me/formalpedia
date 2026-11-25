-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.IsLocal.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:05:19.202109+00:00
-- url     : https://prove2.me/submissions/542486ce-e719-4f58-98c2-2e60396a9a26

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
open GroundTheory.Automorphic.Sobolev.IsLocal
variable {T T₁ T₂ : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)}
namespace GroundTheory.Automorphic.Sobolev.IsLocal
theorem _root_.solution (h₁ : IsLocal T₁) (h₂ : IsLocal T₂) : IsLocal (T₁ ∘L T₂) := fun U hU u hu ↦
  h₁ U hU _ (h₂ U hU u hu)
end GroundTheory.Automorphic.Sobolev.IsLocal
