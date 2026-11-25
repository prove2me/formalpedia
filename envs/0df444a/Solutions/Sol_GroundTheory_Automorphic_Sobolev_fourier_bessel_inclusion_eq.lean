-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.fourier_bessel_inclusion_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:34:02.258034+00:00
-- url     : https://prove2.me/submissions/bd92455b-6e2f-4cf4-b933-b5ed934875f1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierInv_smulLeft_fourier_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_rellichOp_apply_ae
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_memLp_two_prod_mul
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_ae_eq_of_integral_schwartz_smul_eq
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_inclusion
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_apply_eq_integral
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_weight_smul_fourierFun
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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {s N : ℝ} (χ : 𝓢(E, ℂ))
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (hN : (Module.finrank ℝ E : ℝ) < 2 * N)
    (u : SobolevSpace E ℂ s)
    (hu : smulLeftCLM ℂ (χ : E → ℂ) (SobolevSpace.toDistribution u) = SobolevSpace.toDistribution u) :
    (𝓕 (SobolevSpace.bessel (s - N) (SobolevSpace.inclusion (by linarith : s - N ≤ s) u)) :
      Lp ℂ 2 (volume : Measure E)) = rellichOp (s := s) χ hN (𝓕 (SobolevSpace.bessel s u)) := by
  set G : Lp ℂ 2 (volume : Measure E) := 𝓕 (SobolevSpace.bessel s u)
  apply Lp.ext
  apply ae_eq_of_integral_schwartz_smul_eq (F := ℂ)
  · exact (Lp.memLp _).locallyIntegrable (by norm_num)
  · exact (Lp.memLp _).locallyIntegrable (by norm_num)
  intro φ _
  set φ' : 𝓢(E, ℂ) := SchwartzMap.smulLeftCLM ℂ (weight (s - N)) φ
  set ψ : 𝓢(E, ℂ) := 𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) (𝓕 φ'))

  have hL : ∫ ξ, φ ξ • (𝓕 (SobolevSpace.bessel (s - N)
      (SobolevSpace.inclusion (by linarith : s - N ≤ s) u)) : Lp ℂ 2 (volume : Measure E)) ξ =
      ∫ η, (∫ ξ, φ' ξ * (𝓕 χ : 𝓢(E, ℂ)) (ξ - η)) * (weight (-s) η * G η) := by
    have e1 : ∫ ξ, φ ξ • (𝓕 (SobolevSpace.bessel (s - N)
        (SobolevSpace.inclusion (by linarith : s - N ≤ s) u)) : Lp ℂ 2 (volume : Measure E)) ξ =
        ∫ ξ, φ' ξ • fourierFun u ξ := by
      apply integral_congr_ae
      filter_upwards [fourierFun_inclusion (by linarith : s - N ≤ s) u] with ξ hξ
      rw [← weight_smul_fourierFun, hξ, SchwartzMap.smulLeftCLM_apply_apply
        (weight_hasTemperateGrowth _)]
      simp only [smul_eq_mul]; ring
    have e2 : SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) (𝓕 φ') = 𝓕 ψ := by
      simp only [ψ, FourierTransform.fourier_fourierInv_eq]
    rw [e1, ← fourier_apply_eq_integral, ← hu, TemperedDistribution.fourier_apply,
      smulLeftCLM_apply_apply, e2, ← TemperedDistribution.fourier_apply, fourier_apply_eq_integral]
    congr 1; ext η
    rw [fourierInv_smulLeft_fourier_apply, fourierFun, smul_eq_mul, smul_eq_mul]

  have hint : Integrable (fun p : E × E ↦ φ p.1 * rellichKernel s N χ p * G p.2)
      ((volume : Measure E).prod volume) := by
    have := (memLp_rellichKernel (s := s) χ hN).integrable_mul (memLp_two_prod_mul φ G)
    refine this.congr (ae_of_all _ fun p ↦ ?_)
    simp only [Pi.mul_apply]; ring
  have hR : ∫ ξ, φ ξ • (rellichOp (s := s) χ hN G : Lp ℂ 2 (volume : Measure E)) ξ =
      ∫ η, (∫ ξ, φ' ξ * (𝓕 χ : 𝓢(E, ℂ)) (ξ - η)) * (weight (-s) η * G η) := by
    have e1 : ∫ ξ, φ ξ • (rellichOp (s := s) χ hN G : Lp ℂ 2 (volume : Measure E)) ξ =
        ∫ ξ, ∫ η, φ ξ * rellichKernel s N χ (ξ, η) * G η := by
      apply integral_congr_ae
      filter_upwards [rellichOp_apply_ae (s := s) χ hN G] with ξ hξ
      rw [hξ, smul_eq_mul, ← integral_const_mul]
      congr 1; ext η; ring
    rw [e1, integral_integral_swap hint]
    congr 1; ext η
    rw [← integral_mul_const]
    congr 1; ext ξ
    simp only [rellichKernel, φ', SchwartzMap.smulLeftCLM_apply_apply (weight_hasTemperateGrowth _),
      smul_eq_mul]
    ring
  rw [hL, hR]
end GroundTheory.Automorphic.Sobolev
