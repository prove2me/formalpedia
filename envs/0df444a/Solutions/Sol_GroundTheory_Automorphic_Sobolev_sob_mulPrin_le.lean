-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sob_mulPrin_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:19:28.680281+00:00
-- url     : https://prove2.me/submissions/74dba55a-3bcd-4b01-8bb4-60f2a48770ab

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_eLpNorm_fourier_schwartz
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_fourierMultiplierCLM_weight_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_ofSchwartz_eq
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_ofSchwartz
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_le_of_schwartz
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_mulPrin_coe
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
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
theorem _root_.solution (χ : 𝓢(E, ℂ)) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, ‖χ x‖ ≤ M) (r : ℝ)
    {u : 𝓢'(E, ℂ)} (hu : MemSobolev r 2 u) :
    sob r (mulPrin χ r u) ≤ ENNReal.ofReal M * sob r u := by
  refine sob_le_of_schwartz _ hM0 (fun φ ↦ ?_) hu
  rw [mulPrin_coe, sob_ofSchwartz, sob_ofSchwartz, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul hM0]
  apply ENNReal.ofReal_le_ofReal
  set g : 𝓢(E, ℂ) := SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ)
    (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ)
  have e1 : (fun ξ ↦ weight r ξ * (𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight (-r)) g) :
      𝓢(E, ℂ)) ξ) = ⇑(𝓕 g : 𝓢(E, ℂ)) := by
    ext ξ
    rw [fourier_fourierMultiplierCLM_weight_apply, ← mul_assoc, weight_mul_weight, add_neg_cancel]
    simp [weight]
  have e2 : (fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) =
      ⇑(𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) : 𝓢(E, ℂ)) := by
    ext ξ; rw [fourier_fourierMultiplierCLM_weight_apply]
  rw [norm_ofSchwartz_eq, norm_ofSchwartz_eq, e1, e2, eLpNorm_fourier_schwartz,
    eLpNorm_fourier_schwartz]
  have hle : eLpNorm g 2 volume ≤
      ENNReal.ofReal M * eLpNorm (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) 2 volume := by
    have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (p := 2) (μ := (volume : Measure E))
      (f := g) (g := SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) (c := M.toNNReal)
      (ae_of_all _ fun x ↦ ?_)
    · rw [ENNReal.ofReal]; exact this
    · rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm, Real.coe_toNNReal _ hM0]
      simp only [g, SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, smul_eq_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  have hfin := ((SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ).memLp 2 volume).eLpNorm_lt_top
  calc (eLpNorm g 2 volume).toReal ≤
      (ENNReal.ofReal M * eLpNorm (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hle
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0]
end GroundTheory.Automorphic.Sobolev
