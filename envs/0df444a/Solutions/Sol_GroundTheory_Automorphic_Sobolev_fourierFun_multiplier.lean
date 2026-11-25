-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.fourierFun_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:25:38.486096+00:00
-- url     : https://prove2.me/submissions/054cef68-2ebf-4177-b135-a8596788c7f7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_fourierMultiplierCLM_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_aestronglyMeasurable
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_apply_eq_integral
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_sq_eq_integral_of_fourier
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_weight_smul_fourierFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply



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
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (hm : m.HasTemperateGrowth)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) (u : SobolevSpace E F s) :
    fourierFun (SobolevSpace.multiplier hm hC u) =ᵐ[volume] (fun ξ ↦ m ξ • fourierFun u ξ) ∧
      ‖SobolevSpace.multiplier hm hC u‖ ^ 2 =
        ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ t * ‖m ξ • fourierFun u ξ‖ ^ 2 := by
  have hmem : MemLp (fun ξ ↦ weight t ξ • (m ξ • fourierFun u ξ)) 2 (volume : Measure E) := by
    refine (memLp_smul_of_bounded (hasTemperateGrowth_mul_weight hm (t - s)) (bounded_mul_weight hC)
      (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E))).congr_norm ?_ ?_
    · exact (weight_hasTemperateGrowth t).1.continuous.aestronglyMeasurable.smul
        (hm.1.continuous.aestronglyMeasurable.smul (fourierFun_aestronglyMeasurable u))
    · refine ae_of_all _ fun ξ ↦ ?_
      have e : m ξ * weight (t - s) ξ * weight s ξ = weight t ξ * m ξ := by
        rw [mul_assoc, weight_mul_weight, sub_add_cancel, mul_comm]
      rw [← weight_smul_fourierFun]
      simp only [smul_smul]
      rw [e]
  have hrep : ∀ φ : 𝓢(E, ℂ), 𝓕 (SobolevSpace.toDistribution (SobolevSpace.multiplier hm hC u)) φ =
      ∫ ξ, φ ξ • (m ξ • fourierFun u ξ) := by
    intro φ
    rw [SobolevSpace.toDistribution_multiplier, fourier_fourierMultiplierCLM_apply,
      fourier_apply_eq_integral]
    congr 1; ext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply hm, smul_smul, smul_eq_mul, mul_comm]
  have h := norm_sq_eq_integral_of_fourier _ _ hmem hrep
  exact ⟨h.1.symm, h.2⟩
end GroundTheory.Automorphic.Sobolev
