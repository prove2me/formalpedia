-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.enorm_weight_mul_fourier_commRem_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:52:12.031938+00:00
-- url     : https://prove2.me/submissions/0c6bd80a-d193-48a4-ad46-856010ccdd27

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_abs_weight_sub_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_weight_mul_fourier_commRem
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_weight_sub_weight
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_commConst_nonneg
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_peetre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_sub
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply



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
theorem _root_.solution (r a : ℝ) (φ : 𝓢(E, ℂ)) (ξ : E) :
    ‖weight (r + a) ξ * (𝓕 (commRem χ r φ) : 𝓢(E, ℂ)) ξ‖ₑ ≤
      ∫⁻ η, ENNReal.ofReal (commConst r a) * wK ((|a| + |r - 1| + 1) / 2) (𝓕 χ) (ξ - η) *
        ‖weight (r + a - 1) η * (𝓕 φ : 𝓢(E, ℂ)) η‖ₑ := by
  rw [show r + a = a + r by ring, ← weight_mul_weight a r, mul_assoc, weight_mul_fourier_commRem,
    ← integral_const_mul]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun η ↦ ?_)
  rw [wK, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (commConst_nonneg r a),
    ← ENNReal.ofReal_mul (by have := commConst_nonneg r a; positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_weight, norm_weight,
    norm_weight_sub_weight]
  set X : ℝ := 1 + ‖ξ - η‖ ^ 2
  set Y : ℝ := 1 + ‖η‖ ^ 2
  have hX : 0 < X := by positivity
  have hY : 0 < Y := by positivity
  have hpa := peetre (a / 2) ξ η
  rw [abs_div, abs_two] at hpa
  have hd := abs_weight_sub_le r ξ η
  have hn : ‖ξ - η‖ ≤ X ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]; apply Real.le_sqrt_of_sq_le; simp only [X]; linarith
  have eX : X ^ (|a| / 2) * X ^ (|r - 1| / 2) * X ^ (1 / 2 : ℝ) = X ^ ((|a| + |r - 1| + 1) / 2) := by
    rw [← Real.rpow_add hX, ← Real.rpow_add hX]; congr 1; ring
  have eY : Y ^ (a / 2) * Y ^ ((r - 1) / 2) = Y ^ ((a + r - 1) / 2) := by
    rw [← Real.rpow_add hY]; congr 1; ring
  set A := ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖
  set Φ := ‖(𝓕 φ : 𝓢(E, ℂ)) η‖
  have hA : 0 ≤ A := norm_nonneg _
  have hΦ : 0 ≤ Φ := norm_nonneg _
  calc (1 + ‖ξ‖ ^ 2) ^ (a / 2) * (A * (|(1 + ‖ξ‖ ^ 2) ^ (r / 2) - Y ^ (r / 2)| * Φ))
      ≤ (2 ^ (|a| / 2) * X ^ (|a| / 2) * Y ^ (a / 2)) *
          (A * ((|r| * 2 ^ (|r - 1| / 2) * ‖ξ - η‖ * X ^ (|r - 1| / 2) * Y ^ ((r - 1) / 2)) * Φ)) := by
        gcongr
    _ ≤ (2 ^ (|a| / 2) * X ^ (|a| / 2) * Y ^ (a / 2)) *
          (A * ((|r| * 2 ^ (|r - 1| / 2) * X ^ (1 / 2 : ℝ) * X ^ (|r - 1| / 2) *
            Y ^ ((r - 1) / 2)) * Φ)) := by gcongr
    _ = commConst r a * (X ^ (|a| / 2) * X ^ (|r - 1| / 2) * X ^ (1 / 2 : ℝ)) * A *
          ((Y ^ (a / 2) * Y ^ ((r - 1) / 2)) * Φ) := by unfold commConst; ring
    _ = _ := by rw [eX, eY]; ring
end GroundTheory.Automorphic.Sobolev
