-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.tendsto_smoothed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:49:09.741802+00:00
-- url     : https://prove2.me/submissions/bd5f342c-ee4f-413c-b9bd-9e52f14ef292

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_continuous_phi
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_smoothed_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_bn_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CharDensity
open scoped FourierTransform
open Filter
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SW.CharDensity
theorem _root_.solution (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume)
    (y : V) :
    Tendsto (fun n : ℕ => ((∫ z, ker (bn n) (z - y) ∂μ : ℝ) : ℂ)) atTop (𝓝 (dens μ y)) := by
  simp_rw [← smoothed_eq μ (bn_pos _) y]
  unfold dens
  have hcp := continuous_phi μ
  refine tendsto_integral_of_dominated_convergence (fun x => ‖phi μ x‖) (fun n => ?_) hφ.norm
    (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · rw [norm_mul, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    have h2 : ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have h1 : ‖Complex.exp (-(bn n : ℂ) * (‖x‖ : ℂ) ^ 2)‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      have := (bn_pos n).le
      simp only [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
        Complex.ofReal_re]
      nlinarith [sq_nonneg ‖x‖]
    rw [h2, mul_one]
    exact h1
  · have hc : Continuous (fun t : ℝ => phi μ x * (Complex.exp (-(t : ℂ) * (‖x‖ : ℂ) ^ 2) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ)))) := by
      fun_prop
    have hb : Tendsto bn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have := (hc.tendsto 0).comp hb
    simpa [Function.comp_def] using this
end GlobalTheory.CompanionTheory.SW.CharDensity
