-- Prove2me | solution 1 for HessianDamping.IPAHDSC.term2_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:22:35.332992+00:00
-- url     : https://prove2.me/submissions/802a3117-e5ae-475a-81c9-07d38f9a3709

import Mathlib
set_option autoImplicit false

theorem solution (μ β s : ℝ) (hμ : 0 < μ) (hs : 0 < s) (hβ : 0 < β) :
    (Real.sqrt μ / (2 * s) + μ / Real.sqrt s ≥ μ / β →
      ∀ X Y : ℝ,
        0 ≤ (Real.sqrt μ / (2 * s) + μ / Real.sqrt s) * X ^ 2 + β / 4 * Y ^ 2 -
          Real.sqrt μ * X * Y) ∧
    (Real.sqrt μ / (2 * s) + μ / Real.sqrt s ≥ μ / β ↔
      Real.sqrt s ≤ β / 2 * (1 + Real.sqrt (1 + 2 / (β * Real.sqrt μ)))) ∧
    (Real.sqrt s ≤ β → Real.sqrt μ / (2 * s) + μ / Real.sqrt s ≥ μ / β) := by
  have hr : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hμr : μ = Real.sqrt μ ^ 2 := (Real.sq_sqrt hμ.le).symm
  have hsq : s = Real.sqrt s ^ 2 := (Real.sq_sqrt hs.le).symm
  set r := Real.sqrt μ with hrdef
  set q := Real.sqrt s with hqdef
  set A := r / (2 * s) + μ / q with hA
  have hApos : 0 < A := by positivity
  -- part 1
  have part1 : A ≥ μ / β → ∀ X Y : ℝ, 0 ≤ A * X ^ 2 + β / 4 * Y ^ 2 - r * X * Y := by
    intro h X Y
    have h' : μ ≤ A * β := by
      have := (div_le_iff₀ hβ).mp h
      exact this
    have h'' : r ^ 2 ≤ A * β := by rw [← hμr]; exact h'
    have e : 4 * A * (A * X ^ 2 + β / 4 * Y ^ 2 - r * X * Y)
        = (2 * A * X - r * Y) ^ 2 + (A * β - r ^ 2) * Y ^ 2 := by ring
    have : 0 ≤ 4 * A * (A * X ^ 2 + β / 4 * Y ^ 2 - r * X * Y) := by
      rw [e]; have := mul_nonneg (sub_nonneg.mpr h'') (sq_nonneg Y); positivity
    by_contra hneg
    push_neg at hneg
    nlinarith
  -- equivalence
  set c := Real.sqrt (1 + 2 / (β * r)) with hc
  have hc2 : c ^ 2 = 1 + 2 / (β * r) := Real.sq_sqrt (by positivity)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc2' : β * r * c ^ 2 = β * r + 2 := by
    rw [hc2]; field_simp
  have hc1 : 1 ≤ c := by nlinarith [show (0:ℝ) ≤ 2 / (β * r) by positivity]
  have hdiff : A - μ / β = r * (β + 2 * r * q * β - 2 * r * q ^ 2) / (2 * q ^ 2 * β) := by
    simp only [hA]
    rw [hμr, hsq]
    field_simp
  set N := β + 2 * r * q * β - 2 * r * q ^ 2 with hN
  have hNeq : N = 2 * r * ((β * c / 2) ^ 2 - (q - β / 2) ^ 2) := by
    rw [hN]; linear_combination (-(β / 2)) * hc2'
  have hAiff : A ≥ μ / β ↔ 0 ≤ N := by
    have hden : 0 < 2 * q ^ 2 * β := by positivity
    constructor
    · intro h
      have h0 : 0 ≤ A - μ / β := sub_nonneg.mpr h
      rw [hdiff] at h0
      have := (le_div_iff₀ hden).mp h0
      simp only [zero_mul] at this
      exact nonneg_of_mul_nonneg_right this hr
    · intro h
      have : 0 ≤ A - μ / β := by
        rw [hdiff]; positivity
      linarith
  have hiff : 0 ≤ N ↔ q ≤ β / 2 * (1 + c) := by
    rw [hNeq]
    constructor
    · intro h
      have h' : (q - β / 2) ^ 2 ≤ (β * c / 2) ^ 2 := by
        have : 0 ≤ (β * c / 2) ^ 2 - (q - β / 2) ^ 2 := by
          by_contra hh; push_neg at hh
          have : 2 * r * ((β * c / 2) ^ 2 - (q - β / 2) ^ 2) < 0 :=
            mul_neg_of_pos_of_neg (by positivity) hh
          linarith
        linarith
      have := abs_le_of_sq_le_sq' h' (by positivity)
      nlinarith [this.2]
    · intro h
      have h' : (q - β / 2) ^ 2 ≤ (β * c / 2) ^ 2 := by
        apply sq_le_sq'
        · nlinarith
        · nlinarith
      have : 0 ≤ (β * c / 2) ^ 2 - (q - β / 2) ^ 2 := by linarith
      positivity
  refine ⟨part1, ?_, ?_⟩
  · exact hAiff.trans hiff
  · intro h
    exact hAiff.mpr (hiff.mpr (by nlinarith))
