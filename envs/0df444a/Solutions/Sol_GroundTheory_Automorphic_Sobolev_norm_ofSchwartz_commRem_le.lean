-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_ofSchwartz_commRem_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:04:01.999953+00:00
-- url     : https://prove2.me/submissions/9e3b7ae3-7488-4c93-b8ad-b52fd1d8d6d9

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
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_commConst_nonneg
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_enorm_weight_mul_fourier_commRem_le

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
theorem _root_.solution (r a : ℝ) (φ : 𝓢(E, ℂ)) :
    ‖SobolevSpace.ofSchwartz (r + a) (commRem χ r φ)‖ ≤
      commConst r a * wInt ((|a| + |r - 1| + 1) / 2) (𝓕 χ) *
        ‖SobolevSpace.ofSchwartz (r + a - 1) φ‖ := by
  have h := eLpNorm_le_of_le_conv (((measurable_wK _ (𝓕 χ)).const_mul _))
    (measurable_weight_mul_fourier (r + a - 1) φ) (enorm_weight_mul_fourier_commRem_le χ r a φ)
  rw [lintegral_const_mul _ (measurable_wK _ _), lintegral_wK,
    ← ENNReal.ofReal_mul (commConst_nonneg r a)] at h
  rw [norm_ofSchwartz_eq, norm_ofSchwartz_eq]
  have hfin := eLpNorm_weight_fourier_lt_top (r + a - 1) φ
  calc _ ≤ (ENNReal.ofReal (commConst r a * wInt ((|a| + |r - 1| + 1) / 2) (𝓕 χ)) *
        eLpNorm (fun ξ ↦ weight (r + a - 1) ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) h
    _ = _ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
          (mul_nonneg (commConst_nonneg r a) (wInt_nonneg _ _))]
end GroundTheory.Automorphic.Sobolev
