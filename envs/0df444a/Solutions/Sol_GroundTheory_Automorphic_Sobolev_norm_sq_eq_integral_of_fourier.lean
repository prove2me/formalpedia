-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_sq_eq_integral_of_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:26.080821+00:00
-- url     : https://prove2.me/submissions/72af2cfe-60f8-4069-a08d-9812a3db6c3f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_weight_fourier
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_weight_smul_fourierFun
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_sq_eq_integral

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
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (u : SobolevSpace E F s) (g : E → F)
    (hg : MemLp (fun ξ ↦ weight s ξ • g ξ) 2 (volume : Measure E))
    (hφ : ∀ φ : 𝓢(E, ℂ), 𝓕 (SobolevSpace.toDistribution u) φ = ∫ ξ, φ ξ • g ξ) :
    g =ᵐ[volume] fourierFun u ∧ ‖u‖ ^ 2 = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s * ‖g ξ‖ ^ 2 := by
  have hL : hg.toLp _ = (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E)) := by
    apply toTemperedDistribution_injective
    simp only
    rw [← smulLeftCLM_weight_fourier]
    ext φ
    rw [smulLeftCLM_apply_apply, hφ, Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with ξ hξ
    rw [hξ, SchwartzMap.smulLeftCLM_apply_apply (weight_hasTemperateGrowth s)]
    simp only [smul_smul, smul_eq_mul, mul_comm]
  have hae : (fun ξ ↦ weight s ξ • g ξ) =ᵐ[volume] fun ξ ↦ weight s ξ • fourierFun u ξ := by
    have h2 : ⇑(hg.toLp _) =ᵐ[volume] ⇑(𝓕 (SobolevSpace.bessel s u) :
        Lp F 2 (volume : Measure E)) := by rw [hL]
    filter_upwards [hg.coeFn_toLp, h2] with ξ h1 h2
    rw [← h1, h2, weight_smul_fourierFun]
  have hg' : g =ᵐ[volume] fourierFun u := by
    filter_upwards [hae] with ξ h
    have hw : weight s ξ ≠ 0 := by
      unfold weight; exact_mod_cast (weight_pos s ξ).ne'
    exact smul_right_injective F hw h
  refine ⟨hg', ?_⟩
  rw [norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [hg'] with ξ h
  rw [h]
end GroundTheory.Automorphic.Sobolev
