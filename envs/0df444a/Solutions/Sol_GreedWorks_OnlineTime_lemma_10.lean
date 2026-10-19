-- Prove2me | solution 1 for GreedWorks.OnlineTime.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T08:39:20.948683+00:00
-- url     : https://prove2.me/submissions/f08b72b6-5c96-48d8-982f-f59db6e9425a

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

/-- algebraic core of the case `Δ ≥ 1` -/
lemma gw10_alg (μ m v : ℝ) (hμ : 0 < μ) (hm0 : 0 ≤ m) (hmμ : m ≤ μ) (hv : μ ^ 2 ≤ v)
    (key : ∀ t : ℝ, μ ≤ t → (t + μ) ^ 2 * m ≤ μ * (v + t ^ 2)) :
    m * (v + μ ^ 2) ≤ μ * v := by
  by_cases hc : m ≤ μ / 2
  · nlinarith
  · push_neg at hc
    rcases hmμ.lt_or_eq with hlt | heq
    · have hd : 0 < μ - m := by linarith
      set d := μ - m with hdd
      set t := m * μ / d with ht
      have htd : t * d = m * μ := by rw [ht]; field_simp
      have hμt : μ ≤ t := by
        rw [ht, le_div_iff₀ hd]; nlinarith
      have hk := key t hμt
      have h2 : (t + μ) * d = μ ^ 2 := by
        have : μ = d + m := by rw [hdd]; ring
        nlinarith
      have h3 : ((t + μ) * d) ^ 2 * m ≤ d ^ 2 * (μ * (v + t ^ 2)) := by
        have := mul_le_mul_of_nonneg_left hk (sq_nonneg d)
        nlinarith [this]
      rw [h2] at h3
      have h4 : (μ ^ 2) ^ 2 * m ≤ μ * v * d ^ 2 + μ * (m * μ) ^ 2 := by
        have e : d ^ 2 * (μ * (v + t ^ 2)) = μ * v * d ^ 2 + μ * (t * d) ^ 2 := by ring
        rw [e, htd] at h3
        exact h3
      have h5 : μ ^ 3 * m ≤ v * d ^ 2 + μ ^ 2 * m ^ 2 := by
        have : μ * (μ ^ 3 * m) ≤ μ * (v * d ^ 2 + μ ^ 2 * m ^ 2) := by nlinarith [h4]
        exact le_of_mul_le_mul_left this hμ
      have h6 : μ ^ 2 * m * d ≤ v * d * d := by
        have e : μ ^ 3 * m - μ ^ 2 * m ^ 2 = μ ^ 2 * m * d := by rw [hdd]; ring
        nlinarith [h5, e]
      have h7 : μ ^ 2 * m ≤ v * d := le_of_mul_le_mul_right h6 hd
      rw [hdd] at h7
      nlinarith [h7]
    · exfalso
      subst heq
      have hvm : m ≤ v / m := by rw [le_div_iff₀ hμ]; nlinarith
      have := key (v / m) hvm
      have e : (v / m + m) ^ 2 * m = (v + m ^ 2) ^ 2 / m := by field_simp
      have e2 : m * (v + (v / m) ^ 2) = (v * m ^ 2 + v ^ 2) / m := by field_simp
      rw [e, e2, div_le_div_iff_of_pos_right hμ] at this
      nlinarith [sq_nonneg (v + m ^ 2), mul_pos hμ hμ]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : Ω → ℝ) (hX0 : ∀ ω, 0 ≤ X ω) (hX : MemLp X 2 Pr) (hμ : 0 < ∫ ω, X ω ∂Pr) :
    (variance X Pr / (∫ ω, X ω ∂Pr) ^ 2 ≤ 1 →
      ∫ ω, max (X ω - ∫ ω', X ω' ∂Pr) 0 ∂Pr ≤
        (∫ ω, X ω ∂Pr) * Real.sqrt (variance X Pr / (∫ ω, X ω ∂Pr) ^ 2) / 2) ∧
    (1 ≤ variance X Pr / (∫ ω, X ω ∂Pr) ^ 2 →
      ∫ ω, max (X ω - ∫ ω', X ω' ∂Pr) 0 ∂Pr ≤
        (∫ ω, X ω ∂Pr) * (variance X Pr / (∫ ω, X ω ∂Pr) ^ 2) /
          (variance X Pr / (∫ ω, X ω ∂Pr) ^ 2 + 1)) := by
  have hXi : Integrable X Pr := hX.integrable one_le_two
  have hX2 : Integrable (fun ω => X ω ^ 2) Pr := hX.integrable_sq
  have hvar : variance X Pr = (∫ ω, X ω ^ 2 ∂Pr) - (∫ ω, X ω ∂Pr) ^ 2 := by
    rw [variance_eq_sub hX]; rfl
  generalize hμd : (∫ ω, X ω ∂Pr) = μ at hμ hvar ⊢
  have hMi : Integrable (fun ω => max (X ω - μ) 0) Pr :=
    (hXi.sub (integrable_const μ)).pos_part
  generalize hmd : (∫ ω, max (X ω - μ) 0 ∂Pr) = m
  generalize hE2 : (∫ ω, X ω ^ 2 ∂Pr) = E2 at hvar
  rw [hvar]
  -- integral of a combination
  have hI : ∀ a b c d : ℝ, ∫ ω, (a * X ω ^ 2 + b * X ω + c * max (X ω - μ) 0 + d) ∂Pr
      = a * E2 + b * μ + c * m + d := by
    intro a b c d
    have h1 : Integrable (fun ω => a * X ω ^ 2) Pr := hX2.const_mul a
    have h2 : Integrable (fun ω => b * X ω) Pr := hXi.const_mul b
    have h3 : Integrable (fun ω => c * max (X ω - μ) 0) Pr := hMi.const_mul c
    have h12 : Integrable (fun ω => a * X ω ^ 2 + b * X ω) Pr := h1.add h2
    have h123 : Integrable (fun ω => a * X ω ^ 2 + b * X ω + c * max (X ω - μ) 0) Pr := h12.add h3
    rw [integral_add h123 (integrable_const d), integral_add h12 h3, integral_add h1 h2]
    rw [integral_const_mul, integral_const_mul, integral_const_mul, hE2, hμd, hmd]
    simp
  have hnn : ∀ a b c d : ℝ, (∀ ω, 0 ≤ a * X ω ^ 2 + b * X ω + c * max (X ω - μ) 0 + d) →
      0 ≤ a * E2 + b * μ + c * m + d := by
    intro a b c d h
    rw [← hI]
    exact integral_nonneg h
  have hm0 : 0 ≤ m := by
    rw [← hmd]; exact integral_nonneg (fun ω => le_max_right _ _)
  have hmμ : m ≤ μ := by
    calc m = ∫ ω, max (X ω - μ) 0 ∂Pr := hmd.symm
      _ ≤ ∫ ω, X ω ∂Pr := by
        refine integral_mono hMi hXi (fun ω => ?_)
        exact max_le (by linarith) (hX0 ω)
      _ = μ := hμd
  have hμ2 : 0 < μ ^ 2 := by positivity
  constructor
  · intro _
    have h := hnn 1 (4 * m - 2 * μ) (-8 * m) ((μ - 2 * m) ^ 2) (by
      intro ω
      have hx := hX0 ω
      rcases le_total (X ω - μ) 0 with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg (X ω - μ + 2 * m)]
      · rw [max_eq_left h]; nlinarith [sq_nonneg (X ω - μ - 2 * m)])
    have h4 : (2 * m / μ) ^ 2 ≤ (E2 - μ ^ 2) / μ ^ 2 := by
      rw [div_pow, div_le_div_iff_of_pos_right hμ2]; nlinarith
    have h5 : 2 * m / μ ≤ Real.sqrt ((E2 - μ ^ 2) / μ ^ 2) := Real.le_sqrt_of_sq_le h4
    rw [div_le_iff₀ hμ] at h5
    nlinarith
  · intro h1
    rw [le_div_iff₀ hμ2] at h1
    have hv : μ ^ 2 ≤ E2 - μ ^ 2 := by linarith
    have key : ∀ t : ℝ, μ ≤ t → (t + μ) ^ 2 * m ≤ μ * ((E2 - μ ^ 2) + t ^ 2) := by
      intro t ht
      have h := hnn μ (t ^ 2 - μ ^ 2) (-(t + μ) ^ 2) 0 (by
        intro ω
        have hx := hX0 ω
        rcases le_total (X ω - μ) 0 with h | h
        · rw [max_eq_right h]; nlinarith [mul_nonneg hx hμ.le, mul_nonneg hx (sub_nonneg.2 ht)]
        · rw [max_eq_left h]; nlinarith [mul_nonneg hμ.le (sq_nonneg (X ω - t - μ))])
      nlinarith
    have hcore := gw10_alg μ m (E2 - μ ^ 2) hμ hm0 hmμ hv key
    have e : μ * ((E2 - μ ^ 2) / μ ^ 2) / ((E2 - μ ^ 2) / μ ^ 2 + 1)
        = μ * (E2 - μ ^ 2) / ((E2 - μ ^ 2) + μ ^ 2) := by
      field_simp
    rw [e, le_div_iff₀ (by linarith)]
    linarith
