-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.SobolevSpace.denseRange_ofSchwartz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:43:41.064813+00:00
-- url     : https://prove2.me/submissions/99825c8d-5450-4c3c-8696-c2278ebdc7f2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Theorems.Thm_P2M_GroundTheory_Automorphic_Sobolev_SobolevSpace_bessel___symm_toLp_df79e3edb4b7

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
variable {m : E → ℂ} {C s t : ℝ}
open GroundTheory.Automorphic.Sobolev.SobolevSpace
variable {s : ℝ}
namespace GroundTheory.Automorphic.Sobolev.SobolevSpace
theorem _root_.solution : DenseRange (ofSchwartz (E := E) (F := F) s) := by
  have h : DenseRange (fun ψ : 𝓢(E, F) ↦ (besselₗᵢ (E := E) (F := F) s).symm (ψ.toLp 2)) :=
    (besselₗᵢ s).symm.toHomeomorph.surjective.denseRange.comp
      (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top)
      (besselₗᵢ s).symm.continuous
  refine Dense.mono ?_ h
  rintro _ ⟨ψ, rfl⟩
  exact ⟨_, (besselₗᵢ_symm_toLp ψ).symm⟩
end GroundTheory.Automorphic.Sobolev.SobolevSpace
