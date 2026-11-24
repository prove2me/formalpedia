-- Prove2me | solution 1 for Kyprianou.Ch02.subordinatorUncompensatedExponentV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:58:45.816468+00:00
-- url     : https://prove2.me/submissions/1f4cf1c0-5f16-48d3-a4b3-e8aaa3706bab

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_zero_singleton

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hs : ν (Set.Iio (0 : ℝ)) = 0) (hσ : σ = 0)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) (ξ : ℝ) :
    Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, ν, hν⟩ ξ =
      Complex.I * (((-a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ν) * ξ : ℝ) : ℂ) +
      ∫ x in Set.Ioi (0 : ℝ),
        (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν := by
  have hpos : ∀ᵐ x ∂ν, x ∈ Set.Ioi (0 : ℝ) := by
    rw [ae_iff]
    have he : {x : ℝ | ¬ x ∈ Set.Ioi (0 : ℝ)} = Set.Iio 0 ∪ {0} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_Ioi, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
      exact not_lt.trans le_iff_lt_or_eq
    rw [he]
    exact measure_union_null hs hν.zero_singleton
  have hr : ν.restrict (Set.Ioi (0 : ℝ)) = ν :=
    Measure.restrict_eq_self_of_ae_mem hpos
  rw [hr] at hint
  let l : ℝ → ℝ := (Set.Ioo (0 : ℝ) 1).indicator id
  have hl : Integrable l ν := by
    apply hint.mono'
    · exact (measurable_id.indicator measurableSet_Ioo).aestronglyMeasurable
    · filter_upwards with x
      by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
      · simp [l, Set.indicator_of_mem hx, Real.norm_eq_abs,
          abs_of_pos hx.1, min_eq_right (le_of_lt hx.2)]
      · simp [l, Set.indicator_of_notMem hx, le_min]
  have hc := ProbabilityTheory.integrable_levyCompensatedIntegrand hν ξ
  have hlc : Integrable (fun x => (l x : ℂ) * (ξ : ℂ) * I) ν :=
    (hl.ofReal.mul_const (ξ : ℂ)).mul_const I
  have heq : (fun x : ℝ => Complex.exp (I * ((ξ * x : ℝ) : ℂ)) - 1) =ᵐ[ν]
      (fun x => ProbabilityTheory.levyCompensatedIntegrand ξ x + (l x : ℂ) * (ξ : ℂ) * I) := by
    filter_upwards [hpos] with x hx
    have hx0 : 0 < x := hx
    have he : I * ((ξ * x : ℝ) : ℂ) = (x : ℂ) * (ξ : ℂ) * I := by
      push_cast
      ring
    rw [he]
    by_cases h : x < 1
    · have hm : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, h⟩
      simp [ProbabilityTheory.levyCompensatedIntegrand, l, Set.indicator_of_mem hm,
        abs_of_pos hx0, h]
    · have hm : x ∉ Set.Ioo (0 : ℝ) 1 := fun hh => h hh.2
      simp [ProbabilityTheory.levyCompensatedIntegrand, l, Set.indicator_of_notMem hm,
        abs_of_pos hx0, h]
  have hsum := integral_congr_ae heq
  rw [integral_add hc hlc, integral_mul_const, integral_mul_const, integral_complex_ofReal] at hsum
  have hli : ∫ x, l x ∂ν = ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ν :=
    integral_indicator measurableSet_Ioo
  rw [hli] at hsum
  rw [hσ, Kyprianou.Ch01.levyTripleExponent, hr, hsum]
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), NNReal.coe_zero, zero_mul,
    zero_div, Complex.ofReal_zero, sub_zero]
  push_cast
  ring
