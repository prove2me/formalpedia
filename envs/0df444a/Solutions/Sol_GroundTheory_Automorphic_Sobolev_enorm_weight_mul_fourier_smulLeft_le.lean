-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.enorm_weight_mul_fourier_smulLeft_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:48:34.92194+00:00
-- url     : https://prove2.me/submissions/c8531b70-89d4-48ce-a92d-7288b1308b4b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_smulLeftCLM_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_peetre


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
theorem _root_.solution (r : ℝ) (φ : 𝓢(E, ℂ)) (ξ : E) :
    ‖weight r ξ * (𝓕 (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ) : 𝓢(E, ℂ)) ξ‖ₑ ≤
      ∫⁻ η, ENNReal.ofReal (2 ^ (|r| / 2)) * wK (|r| / 2) (𝓕 χ) (ξ - η) *
        ‖weight r η * (𝓕 φ : 𝓢(E, ℂ)) η‖ₑ := by
  rw [fourier_smulLeftCLM_apply, ← integral_const_mul]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun η ↦ ?_)
  rw [wK, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [norm_mul, norm_mul, norm_mul, norm_weight, norm_weight]
  have hp := peetre (r / 2) ξ η
  rw [abs_div, abs_two] at hp
  calc (1 + ‖ξ‖ ^ 2) ^ (r / 2) * (‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ * ‖(𝓕 φ : 𝓢(E, ℂ)) η‖)
      ≤ (2 ^ (|r| / 2) * (1 + ‖ξ - η‖ ^ 2) ^ (|r| / 2) * (1 + ‖η‖ ^ 2) ^ (r / 2)) *
          (‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ * ‖(𝓕 φ : 𝓢(E, ℂ)) η‖) := by gcongr
    _ = _ := by ring
end GroundTheory.Automorphic.Sobolev
