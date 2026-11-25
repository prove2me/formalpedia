-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_ofSchwartz_smulLeft_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:56.134455+00:00
-- url     : https://prove2.me/submissions/4890bf00-2b3b-48ed-a439-16169fd0b4bb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_eLpNorm_le_of_le_conv
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_ofSchwartz_eq
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_eLpNorm_weight_fourier_lt_top
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_measurable_wK
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_wInt_nonneg
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_lintegral_wK
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_measurable_weight_mul_fourier
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_enorm_weight_mul_fourier_smulLeft_le

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
theorem _root_.solution (r : ℝ) (φ : 𝓢(E, ℂ)) :
    ‖SobolevSpace.ofSchwartz r (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ)‖ ≤
      2 ^ (|r| / 2) * wInt (|r| / 2) (𝓕 χ) * ‖SobolevSpace.ofSchwartz r φ‖ := by
  have h := eLpNorm_le_of_le_conv (((measurable_wK (|r| / 2) (𝓕 χ)).const_mul _))
    (measurable_weight_mul_fourier r φ) (enorm_weight_mul_fourier_smulLeft_le χ r φ)
  rw [lintegral_const_mul _ (measurable_wK _ _), lintegral_wK,
    ← ENNReal.ofReal_mul (by positivity)] at h
  rw [norm_ofSchwartz_eq, norm_ofSchwartz_eq]
  have hfin := eLpNorm_weight_fourier_lt_top r φ
  calc _ ≤ (ENNReal.ofReal (2 ^ (|r| / 2) * wInt (|r| / 2) (𝓕 χ)) *
        eLpNorm (fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) h
    _ = _ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (by positivity) (wInt_nonneg _ _))]
end GroundTheory.Automorphic.Sobolev
