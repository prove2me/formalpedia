-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.IsLocal.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:20.765152+00:00
-- url     : https://prove2.me/submissions/5c4a13f5-271c-46b2-aed1-cafcdcb74241

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_isVanishingOn_smul

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
theorem _root_.solution (h : IsLocal T) (c : ℂ) : IsLocal (c • T) := fun U hU u hu ↦ by
  rw [smul_apply]; exact isVanishingOn_smul c (h U hU u hu)
end GroundTheory.Automorphic.Sobolev.IsLocal
