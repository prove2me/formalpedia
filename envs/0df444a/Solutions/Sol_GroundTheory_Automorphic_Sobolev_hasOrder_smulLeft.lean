-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.hasOrder_smulLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:27:24.139799+00:00
-- url     : https://prove2.me/submissions/d17db316-a7be-488c-bf45-945f4a444515

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_mulConst_nonneg
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_smulLeft_le


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
theorem _root_.solution (χ : 𝓢(E, ℂ)) : HasOrder (smulLeftCLM ℂ (χ : E → ℂ)) 0 := fun s ↦
  ⟨mulConst s χ, mulConst_nonneg s χ, fun u hu ↦ by
    rw [sub_zero]; exact sob_smulLeft_le χ s hu⟩
end GroundTheory.Automorphic.Sobolev
