-- Prove2me | solution 1 for Newton.cutoff_L2_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:14:12.297889+00:00
-- url     : https://prove2.me/submissions/82bdf92a-f74c-43bb-bc02-29ee96e3b64b

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
    (χ : (Fin n → ℝ) → ℝ)
    (R ε_tail₂ : ℝ)
    (hχ_nonneg : ∀ x, 0 ≤ χ x)
    (hχ_le_one : ∀ x, χ x ≤ 1)
    (hf_cut_def : f_cut = fun x => (χ x : ℂ) * f x)
    (h_diff_zero_inside : ∀ {x : Fin n → ℝ}, ‖x‖ ≤ R → f x - f_cut x = 0)
    (hf_tail_L2 :
      eLpNorm (fun x => f x) 2 (volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖})
        < ENNReal.ofReal ε_tail₂) :
    eLpNorm (fun x => f x - f_cut x) 2 volume ≤ ENNReal.ofReal ε_tail₂ := by
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
  have h_pointwise_sq :
      ∀ x,
        ‖f x - f_cut x‖ₑ ^ (2 : ℝ)
          ≤ Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x := by
    intro x
    have hpow := ENNReal.rpow_le_rpow (h_pointwise_le x) (by norm_num : 0 ≤ (2 : ℝ))
    have h_indicator_sq :
        Set.indicator tail (fun x => ‖f x‖ₑ) x ^ (2 : ℝ)
          = Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x := by
      by_cases hx : R ≤ ‖x‖
      · simp [tail, hx]
      · simp [tail, hx]
    simpa [h_indicator_sq]
      using hpow
  have h_lintegral_le :
      ∫⁻ x, ‖f x - f_cut x‖ₑ ^ (2 : ℝ) ∂volume
        ≤ ∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂volume := by
    refine MeasureTheory.lintegral_mono_ae ?_
    exact Filter.Eventually.of_forall h_pointwise_sq
  have h_indicator_eq :
      ∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂volume
        = ∫⁻ x in tail, ‖f x‖ₑ ^ (2 : ℝ) ∂volume := by
    simpa [tail]
      using
        (MeasureTheory.lintegral_indicator
          (μ := volume) (hs := h_tail_meas)
          (f := fun x => ‖f x‖ₑ ^ (2 : ℝ)))
  have h_le_indicator :
      (∫⁻ x, ‖f x - f_cut x‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ))
        ≤ (∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂volume)
            ^ (1 / (2 : ℝ)) :=
    ENNReal.rpow_le_rpow h_lintegral_le (by positivity : 0 ≤ 1 / (2 : ℝ))
  have h_eLp_diff :
      eLpNorm (fun x => f x - f_cut x) 2 volume
        = (∫⁻ x, ‖f x - f_cut x‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
    simpa [ENNReal.toReal_ofNat, one_div]
      using
        (MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (p := (2 : ℝ≥0∞))
            two_ne_zero ENNReal.ofNat_ne_top
            (f := fun x => f x - f_cut x) (μ := volume))
  have h_eLp_tail :
      eLpNorm (fun x => f x) 2 (volume.restrict tail)
        = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume.restrict tail)) ^ (1 / (2 : ℝ)) := by
    simpa [ENNReal.toReal_ofNat, one_div]
      using
        (MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (p := (2 : ℝ≥0∞))
            two_ne_zero ENNReal.ofNat_ne_top
            (f := fun x => f x) (μ := volume.restrict tail))
  have h_le_indicator' :
      eLpNorm (fun x => f x - f_cut x) 2 volume
        ≤ (∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂volume)
            ^ (1 / (2 : ℝ)) := by
    simpa [h_eLp_diff] using h_le_indicator
  have h_indicator_eq_pow :
      (∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂volume)
            ^ (1 / (2 : ℝ))
        = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume.restrict tail)) ^ (1 / (2 : ℝ)) :=
    congrArg (fun t => t ^ (1 / (2 : ℝ))) h_indicator_eq
  have h_le_indicator'' :
      eLpNorm (fun x => f x - f_cut x) 2 volume
        ≤ eLpNorm (fun x => f x) 2 (volume.restrict tail) := by
    calc
      eLpNorm (fun x => f x - f_cut x) 2 volume
          ≤ (∫⁻ x, Set.indicator tail (fun x => ‖f x‖ₑ ^ (2 : ℝ)) x ∂volume)
              ^ (1 / (2 : ℝ)) := h_le_indicator'
      _ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume.restrict tail)) ^ (1 / (2 : ℝ)) := by
            simpa using h_indicator_eq_pow
      _ = eLpNorm (fun x => f x) 2 (volume.restrict tail) := by
            simp [h_eLp_tail, one_div]
  exact h_le_indicator''.trans (le_of_lt hf_tail_L2)
end Newton
