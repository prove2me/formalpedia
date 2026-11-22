-- Prove2me | solution 1 for HellingerSubadd.lemmaA10_klDiv_le
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T08:48:21.570179+00:00
-- url     : https://prove2.me/submissions/297b8abb-e2b2-45ed-ba80-e692ba5e4f39

import Mathlib
import Definitions.Def_HellingerSubadd_hellingerSq

open MeasureTheory InformationTheory
open scoped ENNReal

namespace A10Aux

/-- `log s ≤ 2 (s - 1) / (s + 1)` for `0 < s ≤ 1`, in multiplied-out form. -/
lemma log_mul_le_of_le_one {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    Real.log s * (s + 1) ≤ 2 * (s - 1) := by
  set x : ℝ := (s - 1) / (s + 1) with hx
  have hx0 : x ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hxa : |x| < 1 := by
    rw [abs_lt]; constructor
    · rw [hx, lt_div_iff₀ (by linarith)]; linarith
    · linarith
  have hsum := Real.hasSum_log_sub_log_of_abs_lt_one hxa
  have hlog : Real.log (1 + x) - Real.log (1 - x) = Real.log s := by
    have h1 : 1 + x = 2 * s / (s + 1) := by rw [hx]; field_simp; ring
    have h2 : 1 - x = 2 / (s + 1) := by rw [hx]; field_simp; ring
    rw [← Real.log_div (by rw [h1]; positivity) (by rw [h2]; positivity), h1, h2]
    congr 1; field_simp
  rw [hlog] at hsum
  have hle : Real.log s ≤ 2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * x ^ (2 * 0 + 1) := by
    have := sum_le_hasSum (f := fun k : ℕ => -((2 : ℝ) * (1 / (2 * k + 1)) * x ^ (2 * k + 1)))
      ({0} : Finset ℕ) (fun k _ => by
        have : x ^ (2 * k + 1) ≤ 0 := Odd.pow_nonpos ⟨k, rfl⟩ hx0
        have : (0 : ℝ) ≤ 2 * (1 / (2 * k + 1)) := by positivity
        nlinarith) hsum.neg
    simpa using this
  simp only [CharP.cast_eq_zero, mul_zero, zero_add, div_one, mul_one, pow_one] at hle
  have : 2 * x * (s + 1) = 2 * (s - 1) := by rw [hx]; field_simp
  nlinarith

/-- `2 s log s ≤ s² - 1` for `s ≥ 1`. -/
lemma two_mul_log_le {s : ℝ} (hs : 1 ≤ s) : 2 * s * Real.log s ≤ s ^ 2 - 1 := by
  have hs0 : 0 < s := by linarith
  have h := Real.self_le_sinh_iff.2 (Real.log_nonneg hs)
  rw [Real.sinh_log hs0] at h
  have : (s - s⁻¹) / 2 * (2 * s) = s ^ 2 - 1 := by field_simp
  nlinarith

/-- Pointwise inequality: `klFun t ≤ (2 + log V) (√t - 1)²` for `0 ≤ t ≤ V`, `1 ≤ V`. -/
lemma klFun_le {t V : ℝ} (ht : 0 ≤ t) (htV : t ≤ V) (hV : 1 ≤ V) :
    klFun t ≤ (2 + Real.log V) * (Real.sqrt t - 1) ^ 2 := by
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hV
  set s := Real.sqrt t with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg t
  have hts : t = s ^ 2 := (Real.sq_sqrt ht).symm
  rw [klFun_apply, hts]
  rcases hs0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp; linarith
  have hlogt : Real.log (s ^ 2) = 2 * Real.log s := by
    rw [Real.log_pow]; norm_num
  rw [hlogt]
  rcases le_total s 1 with hs1 | hs1
  · have hl := log_mul_le_of_le_one hpos hs1
    have key : s ^ 2 * (2 * Real.log s) + 1 - s ^ 2 ≤ 2 * (s - 1) ^ 2 := by
      have hpos' : 0 < s + 1 := by linarith
      refine le_of_mul_le_mul_left ?_ hpos'
      have h3 : 0 ≤ (1 - s) ^ 3 := pow_nonneg (by linarith) 3
      have : (s + 1) * (s ^ 2 * (2 * Real.log s)) ≤ 2 * s ^ 2 * (2 * (s - 1)) := by
        nlinarith [sq_nonneg s]
      nlinarith
    nlinarith [sq_nonneg (s - 1)]
  · have hl := two_mul_log_le hs1
    have hlog0 : 0 ≤ Real.log s := Real.log_nonneg hs1
    have hlogs : 2 * Real.log s ≤ Real.log V := by
      rw [← hlogt, ← hts]; exact Real.log_le_log (by rw [hts]; positivity) htV
    have key : s ^ 2 * (2 * Real.log s) + 1 - s ^ 2 ≤ (2 + 2 * Real.log s) * (s - 1) ^ 2 := by
      refine le_of_mul_le_mul_left ?_ hpos
      have h2 : 0 ≤ 2 * s - 1 := by linarith
      have : (2 * s - 1) * (s - 1) * (2 * s * Real.log s) ≤ (2 * s - 1) * (s - 1) * (s ^ 2 - 1) :=
        mul_le_mul_of_nonneg_left hl (mul_nonneg h2 (by linarith))
      nlinarith [pow_nonneg (sub_nonneg.2 hs1) 3]
    nlinarith [sq_nonneg (s - 1)]

end A10Aux

theorem solution {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (V : ℝ)
    (hV : ∀ F, MeasurableSet F → μ F ≤ ENNReal.ofReal V * ν F) :
    klDiv μ ν ≤ ENNReal.ofReal (2 + Real.log V) * HellingerSubadd.hellingerSq μ ν := by
  have hV1 : 1 ≤ V := by
    have h := hV Set.univ MeasurableSet.univ
    simp only [measure_univ, mul_one] at h
    exact (ENNReal.one_le_ofReal).1 h
  have hac : μ ≪ ν := by
    intro F hF
    have h1 := hV (toMeasurable ν F) (measurableSet_toMeasurable ν F)
    rw [measure_toMeasurable, hF, mul_zero] at h1
    exact le_antisymm ((measure_mono (subset_toMeasurable ν F)).trans h1) bot_le
  have hr : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≤ ENNReal.ofReal V := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
      fun s hs _ => ?_
    rw [Measure.setLIntegral_rnDeriv hac, setLIntegral_const]
    exact hV s hs
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  -- Hellinger lower bound
  have hμξ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hνξ : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  have hH : ∫⁻ x, ENNReal.ofReal ((Real.sqrt (μ.rnDeriv ν x).toReal - 1) ^ 2) ∂ν
      ≤ HellingerSubadd.hellingerSq μ ν := by
    calc ∫⁻ x, ENNReal.ofReal ((Real.sqrt (μ.rnDeriv ν x).toReal - 1) ^ 2) ∂ν
        = ∫⁻ x, ENNReal.ofReal ((Real.sqrt (μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x).toReal
            - 1) ^ 2) ∂ν := by
          refine lintegral_congr_ae ?_
          filter_upwards [Measure.rnDeriv_eq_div hμξ hνξ] with x hx
          rw [hx]
      _ = ∫⁻ x, ν.rnDeriv (μ + ν) x * ENNReal.ofReal ((Real.sqrt
            (μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x).toReal - 1) ^ 2) ∂(μ + ν) := by
          rw [lintegral_rnDeriv_mul hνξ (by fun_prop)]
      _ ≤ HellingerSubadd.hellingerSq μ ν := by
          unfold HellingerSubadd.hellingerSq
          refine lintegral_mono_ae ?_
          filter_upwards [Measure.rnDeriv_lt_top μ (μ + ν), Measure.rnDeriv_lt_top ν (μ + ν)]
            with x hp hq
          set p := μ.rnDeriv (μ + ν) x
          set q := ν.rnDeriv (μ + ν) x
          rcases eq_or_ne q 0 with hq0 | hq0
          · rw [hq0, zero_mul]; exact bot_le
          have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq.ne
          have e : q = ENNReal.ofReal q.toReal := (ENNReal.ofReal_toReal hq.ne).symm
          rw [ENNReal.toReal_div]
          refine le_of_eq ?_
          calc q * ENNReal.ofReal ((Real.sqrt (p.toReal / q.toReal) - 1) ^ 2)
              = ENNReal.ofReal q.toReal *
                  ENNReal.ofReal ((Real.sqrt (p.toReal / q.toReal) - 1) ^ 2) := by rw [← e]
            _ = ENNReal.ofReal ((Real.sqrt p.toReal - Real.sqrt q.toReal) ^ 2) := ?_
          rw [← ENNReal.ofReal_mul hqr.le]
          refine congrArg ENNReal.ofReal ?_
          rw [Real.sqrt_div' _ hqr.le]
          have hsq : 0 < Real.sqrt q.toReal := Real.sqrt_pos.2 hqr
          rw [show q.toReal * (Real.sqrt p.toReal / Real.sqrt q.toReal - 1) ^ 2
              = (Real.sqrt q.toReal * (Real.sqrt p.toReal / Real.sqrt q.toReal - 1)) ^ 2 by
            rw [mul_pow, Real.sq_sqrt hqr.le]]
          congr 1
          field_simp
  calc ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal (2 + Real.log V) *
          ENNReal.ofReal ((Real.sqrt (μ.rnDeriv ν x).toReal - 1) ^ 2) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hr] with x hx
        rw [← ENNReal.ofReal_mul (by linarith [Real.log_nonneg hV1])]
        exact ENNReal.ofReal_le_ofReal (A10Aux.klFun_le ENNReal.toReal_nonneg
          (ENNReal.toReal_le_of_le_ofReal (by linarith) hx) hV1)
    _ = ENNReal.ofReal (2 + Real.log V) *
          ∫⁻ x, ENNReal.ofReal ((Real.sqrt (μ.rnDeriv ν x).toReal - 1) ^ 2) ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by gcongr
