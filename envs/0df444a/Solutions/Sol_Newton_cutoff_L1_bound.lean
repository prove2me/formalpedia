-- Prove2me | solution 1 for Newton.cutoff_L1_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:13:49.407111+00:00
-- url     : https://prove2.me/submissions/9033e2a4-0438-4396-974b-63b96c3ac3ba

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity
import Definitions.Def_Newton_Analysis_Convolution_Bounds
import Definitions.Def_Newton_Analysis_Distribution_SchwartzDensity

set_option autoImplicit false
open MeasureTheory SchwartzMap Complex NNReal
open scoped ENNReal ContDiff Topology Convolution ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f : (Fin n → ℝ) → ℂ) (f_cut : (Fin n → ℝ) → ℂ)
    (hf_L1 : MemLp f 1 volume)
    (χ : (Fin n → ℝ) → ℝ)
    (R ε_tail₁ : ℝ)
    (hχ_nonneg : ∀ x, 0 ≤ χ x)
    (hχ_le_one : ∀ x, χ x ≤ 1)
    (hf_cut_def : f_cut = fun x => (χ x : ℂ) * f x)
    (h_diff_zero_inside : ∀ {x : Fin n → ℝ}, ‖x‖ ≤ R → f x - f_cut x = 0)
    (hf_tail_L1 :
      ∫ x, ‖f x‖ ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) < ε_tail₁)
    (htail₁ : 0 < ε_tail₁) :
    eLpNorm (fun x => f x - f_cut x) 1 volume ≤ ENNReal.ofReal ε_tail₁ := by
  let tail : Set (Fin n → ℝ) := {x | R ≤ ‖x‖}
  have h_tail_meas : MeasurableSet tail :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have h_pointwise_le :
      ∀ x,
        ‖f x - f_cut x‖ₑ
          ≤ Set.indicator tail (fun x => ‖f x‖ₑ) x := by
    intro x
    by_cases hx : R ≤ ‖x‖
    · have h_abs_nonneg : 0 ≤ 1 - χ x := by
        have := hχ_le_one x
        have hχx_nonneg := hχ_nonneg x
        linarith
      have h_abs_le_one : 1 - χ x ≤ 1 := by
        have hχx_nonneg := hχ_nonneg x
        linarith
      have h_norm_eq : ‖f x - f_cut x‖ = (1 - χ x) * ‖f x‖ := by
        have hfactor : f x - f_cut x = f x * (1 - (χ x : ℂ)) := by
          have := (mul_sub (f x) (1 : ℂ) (χ x : ℂ))
          simpa [hf_cut_def, one_mul, mul_comm, mul_left_comm] using this.symm
        have hnormχ : ‖1 - (χ x : ℂ)‖ = |1 - χ x| := by
          simpa [Complex.ofReal_sub]
            using (RCLike.norm_ofReal (K := ℂ) (1 - χ x))
        have h_abs : |1 - χ x| = 1 - χ x := abs_of_nonneg h_abs_nonneg
        calc
          ‖f x - f_cut x‖
              = ‖f x * (1 - (χ x : ℂ))‖ := by simp [hfactor]
          _ = ‖f x‖ * ‖1 - (χ x : ℂ)‖ := norm_mul _ _
          _ = ‖f x‖ * |1 - χ x| := by simp [hnormχ]
          _ = (1 - χ x) * ‖f x‖ := by simp [h_abs, mul_comm]
      have h_mul_le : (1 - χ x) * ‖f x‖ ≤ ‖f x‖ := by
        have hnorm_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
        have := mul_le_mul_of_nonneg_right h_abs_le_one hnorm_nonneg
        simpa [one_mul] using this
      have h_indicator :
          Set.indicator tail (fun x => ‖f x‖ₑ) x = ‖f x‖ₑ := by
        simp [tail, hx]
      have h_le :
          ENNReal.ofReal ((1 - χ x) * ‖f x‖)
            ≤ ENNReal.ofReal ‖f x‖ :=
        ENNReal.ofReal_le_ofReal h_mul_le
      have h_norm_eq_enorm :
          ‖f x - f_cut x‖ₑ = ENNReal.ofReal ((1 - χ x) * ‖f x‖) := by
        have := congrArg ENNReal.ofReal h_norm_eq
        simpa [ofReal_norm_eq_enorm] using this
      simpa [h_norm_eq_enorm, h_indicator, ofReal_norm_eq_enorm]
        using h_le
    · have hx_lt : ‖x‖ < R := lt_of_not_ge hx
      have hx_not_tail : x ∉ tail := by
        intro hx_mem
        exact hx ((hx_mem : R ≤ ‖x‖))
      have h_zero : f x - f_cut x = 0 := h_diff_zero_inside (le_of_lt hx_lt)
      simp [tail, hx_not_tail, h_zero]
  have h_lintegral_le :
      ∫⁻ x, ‖f x - f_cut x‖ₑ ∂volume
        ≤ ∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ) x ∂volume := by
    refine MeasureTheory.lintegral_mono_ae ?_
    exact Filter.Eventually.of_forall h_pointwise_le
  have h_indicator_eq :
      ∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ) x ∂volume
        = ∫⁻ x in tail, ‖f x‖ₑ ∂volume := by
    simpa [tail]
      using
        (MeasureTheory.lintegral_indicator
          (μ := volume) (hs := h_tail_meas)
          (f := fun x => ‖f x‖ₑ))
  have hf_integrable : Integrable f volume :=
    (memLp_one_iff_integrable).1 hf_L1
  have hf_restrict_integrable : Integrable f (volume.restrict tail) :=
    hf_integrable.restrict (s := tail)
  have h_tail_lintegral_eq :
      ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict tail)
        = ENNReal.ofReal (∫ x, ‖f x‖ ∂(volume.restrict tail)) := by
    have h_int : Integrable (fun x => ‖f x‖) (volume.restrict tail) :=
      hf_restrict_integrable.norm
    have h_nonneg : 0 ≤ᵐ[volume.restrict tail] fun x => ‖f x‖ :=
      Filter.Eventually.of_forall fun _ => norm_nonneg _
    simpa [ofReal_norm_eq_enorm]
      using
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg).symm
  have h_tail_lt :
      ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict tail)
        < ENNReal.ofReal ε_tail₁ := by
    have hpos : 0 < ε_tail₁ := htail₁
    have h_ofReal_lt :
        ENNReal.ofReal (∫ x, ‖f x‖ ∂(volume.restrict tail))
          < ENNReal.ofReal ε_tail₁ :=
      (ENNReal.ofReal_lt_ofReal_iff hpos).2 (by simpa [tail] using hf_tail_L1)
    simpa [h_tail_lintegral_eq] using h_ofReal_lt
  have h_tail_le :
      ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict tail)
        ≤ ENNReal.ofReal ε_tail₁ := le_of_lt h_tail_lt
  have h_le_indicator :
      eLpNorm (fun x => f x - f_cut x) 1 volume
        ≤ ∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ) x ∂volume := by
    simpa [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      using h_lintegral_le
  calc
    eLpNorm (fun x => f x - f_cut x) 1 volume
        ≤ ∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ) x ∂volume :=
          h_le_indicator
    _ = ∫⁻ x in tail, ‖f x‖ₑ ∂volume := h_indicator_eq
    _ = ∫⁻ x, ‖f x‖ₑ ∂(volume.restrict tail) := rfl
    _ ≤ ENNReal.ofReal ε_tail₁ := h_tail_le
end Newton
