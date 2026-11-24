-- Prove2me | solution 1 for MemQueryFeas.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:43:40.280568+00:00
-- url     : https://prove2.me/submissions/653918f6-1418-48fc-aa0e-db57b9aea5f1

import Mathlib

open MeasureTheory

theorem solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hX01 : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hE : α ≤ ∫ ω, X ω ∂μ) :
    ∃ x : ℝ, 0 < x ∧ x ≤ 1 ∧
      ENNReal.ofReal (α / (3 * x * Real.log (3 / α))) ≤ μ {ω | x ≤ X ω} ∧
      α / (3 * Real.log (3 / α)) ≤ x := by
  have hL : 2 / 3 ≤ Real.log (3 / α) := by
    have h1 := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 3 / α by positivity)
    have h2 : (3 / α)⁻¹ = α / 3 := by rw [inv_div]
    rw [h2] at h1
    linarith
  set L := Real.log (3 / α) with hLdef
  have hLpos : 0 < L := by linarith
  set c := α / (3 * L) with hc
  have hcpos : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]; linarith
  have hcL : c * L = α / 3 := by rw [hc]; field_simp
  by_contra hne
  have hbound : ∀ t ∈ Set.Icc c 1, μ.real {ω | t ≤ X ω} ≤ c * t⁻¹ := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hcpos ht.1
    by_contra h
    rw [not_le] at h
    apply hne
    refine ⟨t, htpos, ht.2, ?_, ht.1⟩
    have heq : α / (3 * t * L) = c * t⁻¹ := by rw [hc]; field_simp
    rw [heq, ← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal h.le
  set g : ℝ → ℝ := fun t => μ.real {ω | t ≤ X ω} with hg
  have hanti : Antitone g := fun s t hst =>
    measureReal_mono (fun ω (hω : t ≤ X ω) => le_trans hst hω)
  have hXint : Integrable X μ :=
    (integrable_const (1:ℝ)).mono' hX.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hX01 ω).1]; exact (hX01 ω).2)
  have hint : ∫ ω, X ω ∂μ = ∫ t in (0:ℝ)..1, g t := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact Integrable.integral_eq_integral_Ioc_meas_le (M := 1) hXint
      (ae_of_all _ fun ω => (hX01 ω).1) (ae_of_all _ fun ω => (hX01 ω).2)
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hanti.intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (hgi 0 c) (hgi c 1)] at hint
  have h1 : ∫ t in (0:ℝ)..c, g t ≤ ∫ t in (0:ℝ)..c, (1:ℝ) :=
    intervalIntegral.integral_mono_on hcpos.le (hgi 0 c) intervalIntegrable_const
      (fun t _ => measureReal_le_one)
  have hinvint : IntervalIntegrable (fun t : ℝ => c * t⁻¹) volume c 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ continuousOn_id
    intro x hx
    rw [Set.uIcc_of_le hc1] at hx
    exact (lt_of_lt_of_le hcpos hx.1).ne'
  have h2 : ∫ t in c..1, g t ≤ ∫ t in c..1, c * t⁻¹ :=
    intervalIntegral.integral_mono_on hc1 (hgi c 1) hinvint (fun t ht => hbound t ht)
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at h1
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hcpos one_pos] at h2
  have hlog : Real.log (1 / c) = L + Real.log L := by
    have : 1 / c = (3 / α) * L := by rw [hc]; field_simp
    rw [this, Real.log_mul (by positivity) hLpos.ne']
  rw [hlog] at h2
  have hlogL : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos hLpos
  have h3 : c * Real.log L ≤ c * (L - 1) := mul_le_mul_of_nonneg_left hlogL hcpos.le
  nlinarith
