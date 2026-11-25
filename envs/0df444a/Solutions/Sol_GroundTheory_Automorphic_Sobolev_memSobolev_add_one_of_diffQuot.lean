-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.memSobolev_add_one_of_diffQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:27:14.732972+00:00
-- url     : https://prove2.me/submissions/ba869e19-d481-4994-b796-0a969ffc9062

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_memSobolev_add_one_of_lintegral
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_tendsto_dqSymbol
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_aestronglyMeasurable
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_multiplier
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_integrable_weight_mul_norm_sq_fourierFun


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
open Filter Topology
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (u : SobolevSpace E F s)
    (h : ∀ v : E, ∃ C, ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖SobolevSpace.diffQuot v t u‖ ≤ C) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) := by
  apply memSobolev_add_one_of_lintegral
  intro v
  obtain ⟨C, hC⟩ := h v
  set f : ℝ → E → ℝ≥0∞ := fun t ξ ↦
    ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖dqSymbol v t ξ • fourierFun u ξ‖ ^ 2)
  have hc : Continuous (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ s) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const
      fun ξ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'
  have hfm : ∀ t, AEMeasurable (f t) (volume : Measure E) := fun t ↦
    (hc.aestronglyMeasurable.mul (((dqSymbol_hasTemperateGrowth v t).1.continuous.aestronglyMeasurable.smul
      (fourierFun_aestronglyMeasurable u)).norm.pow 2)).aemeasurable.ennreal_ofReal
  have hnorm : ∀ t, ∫⁻ ξ, f t ξ = ENNReal.ofReal (‖SobolevSpace.diffQuot v t u‖ ^ 2) := by
    intro t
    have hm := fourierFun_multiplier (dqSymbol_hasTemperateGrowth v t)
      (bound_of_le (s := s) (norm_dqSymbol_le' v t)) u
    change _ = ENNReal.ofReal (‖SobolevSpace.multiplier _ _ u‖ ^ 2)
    rw [hm.2, ofReal_integral_eq_lintegral_ofReal]
    · have hi := integrable_weight_mul_norm_sq_fourierFun
        (SobolevSpace.multiplier (dqSymbol_hasTemperateGrowth v t)
          (bound_of_le (s := s) (norm_dqSymbol_le' v t)) u)
      refine hi.congr ?_
      filter_upwards [hm.1] with ξ hξ
      rw [hξ]
    · exact ae_of_all _ fun ξ ↦ by positivity
  have hlim : ∀ ξ, Tendsto (fun t ↦ f t ξ) (𝓝[≠] 0) (𝓝 (ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s *
      ‖((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ)) • fourierFun u ξ‖ ^ 2))) := by
    intro ξ
    apply ENNReal.tendsto_ofReal
    apply Tendsto.const_mul
    apply Tendsto.pow
    apply Tendsto.norm
    exact (tendsto_dqSymbol v ξ).smul_const _
  have hfatou := lintegral_liminf_le' (μ := (volume : Measure E)) (u := 𝓝[≠] (0 : ℝ)) hfm
  have hleft : ∫⁻ ξ, liminf (fun t ↦ f t ξ) (𝓝[≠] 0) = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s *
      ‖((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ)) • fourierFun u ξ‖ ^ 2) := by
    congr 1; ext ξ; exact (hlim ξ).liminf_eq
  have hright : liminf (fun t ↦ ∫⁻ ξ, f t ξ) (𝓝[≠] 0) ≤ ENNReal.ofReal (C ^ 2) := by
    simp_rw [hnorm]
    apply liminf_le_of_frequently_le'
    apply Eventually.frequently
    filter_upwards [hC] with t ht
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hbound := (hleft ▸ hfatou).trans hright
  have hc2 : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  have hpt : ∀ ξ : E,
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ v ^ 2 * ‖fourierFun u ξ‖ ^ 2) =
        ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s *
          ‖((2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ)) • fourierFun u ξ‖ ^ 2) := by
    intro ξ
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [norm_smul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, h2pi,
      Real.norm_eq_abs, mul_one, mul_pow, mul_pow, mul_pow, sq_abs]
    field_simp
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hbound.trans_lt ENNReal.ofReal_lt_top)
end GroundTheory.Automorphic.Sobolev
