-- Prove2me | solution 1 for GraphAlignment.Possible.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:18:30.304062+00:00
-- url     : https://prove2.me/submissions/8fd4d000-61f9-45dd-a111-0f7e7477e91f

import Mathlib
set_option autoImplicit false

theorem solution (τ q1 q2 : ℝ) (hτ : 0 < τ) (hq1 : 0 ≤ q1) (hq2 : 0 < q2) :
    let f : ℝ → ℝ := fun z => z ^ (-τ) * Real.exp (q2 * (z ^ 2 - 1) + q1 * (z - 1))
    let ζ : ℝ := max (Real.sqrt 2 * Real.exp 1 * q1 / τ) (4 * Real.exp 1 * Real.sqrt (q2 / τ))
    (∃ z, 0 < z ∧ IsMinOn f (Set.Ioi 0) z) ∧
      ∀ z, 0 < z → IsMinOn f (Set.Ioi 0) z →
        f z ≤ ζ ^ τ ∧ z ^ 2 = (τ - q1 * z) / (2 * q2) ∧
          (τ - q1 * z) / (2 * q2) ≤ τ / (2 * q2) := by
  intro f ζ
  -- log form
  have hf : ∀ z : ℝ, 0 < z →
      f z = Real.exp (-τ * Real.log z + (q2 * (z ^ 2 - 1) + q1 * (z - 1))) := by
    intro z hz
    simp only [f]
    rw [Real.rpow_def_of_pos hz, ← Real.exp_add]
    congr 1
    ring
  -- the critical point
  obtain ⟨z0, hz0, hcrit⟩ : ∃ z0 : ℝ, 0 < z0 ∧ 2 * q2 * z0 ^ 2 + q1 * z0 = τ := by
    set D := q1 ^ 2 + 8 * q2 * τ with hD
    have hDpos : 0 < D := by positivity
    have hs : Real.sqrt D ^ 2 = D := Real.sq_sqrt hDpos.le
    have hsq : q1 < Real.sqrt D := by
      apply Real.lt_sqrt_of_sq_lt
      nlinarith [mul_pos hq2 hτ]
    refine ⟨(-q1 + Real.sqrt D) / (4 * q2), by apply div_pos <;> linarith, ?_⟩
    field_simp
    nlinarith [hs]
  -- key inequality
  have key : ∀ z : ℝ, 0 < z →
      q2 * (z - z0) ^ 2 ≤ (-τ * Real.log z + (q2 * (z ^ 2 - 1) + q1 * (z - 1))) -
        (-τ * Real.log z0 + (q2 * (z0 ^ 2 - 1) + q1 * (z0 - 1))) := by
    intro z hz
    have hl : Real.log (z / z0) ≤ z / z0 - 1 := Real.log_le_sub_one_of_pos (div_pos hz hz0)
    rw [Real.log_div hz.ne' hz0.ne'] at hl
    have h1 : τ * (z / z0 - 1) = (2 * q2 * z0 + q1) * (z - z0) := by
      field_simp
      nlinarith [hcrit]
    have h2 : τ * (Real.log z - Real.log z0) ≤ (2 * q2 * z0 + q1) * (z - z0) := by
      rw [← h1]; exact mul_le_mul_of_nonneg_left hl hτ.le
    nlinarith [h2]
  -- minimality of z0
  have hmin0 : IsMinOn f (Set.Ioi 0) z0 := by
    intro z hz
    have hz' : (0:ℝ) < z := hz
    simp only [Set.mem_setOf_eq]
    rw [hf z hz', hf z0 hz0]
    apply Real.exp_le_exp.mpr
    nlinarith [key z hz', sq_nonneg (z - z0), hq2]
  -- bound at z0
  have hζb : 0 < 4 * Real.exp 1 * Real.sqrt (q2 / τ) := by positivity
  have hζ : 0 < ζ := lt_of_lt_of_le hζb (le_max_right _ _)
  have hA : Real.sqrt 2 * Real.exp 1 * q1 ≤ ζ * τ := by
    have : Real.sqrt 2 * Real.exp 1 * q1 / τ ≤ ζ := le_max_left _ _
    exact (div_le_iff₀ hτ).mp this
  have hB : 16 * Real.exp 1 ^ 2 * q2 ≤ ζ ^ 2 * τ := by
    have h : 4 * Real.exp 1 * Real.sqrt (q2 / τ) ≤ ζ := le_max_right _ _
    have h' := pow_le_pow_left₀ hζb.le h 2
    have e1 : (4 * Real.exp 1 * Real.sqrt (q2 / τ)) ^ 2 = 16 * Real.exp 1 ^ 2 * (q2 / τ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    rw [e1] at h'
    have : 16 * Real.exp 1 ^ 2 * q2 / τ ≤ ζ ^ 2 := by
      calc 16 * Real.exp 1 ^ 2 * q2 / τ = 16 * Real.exp 1 ^ 2 * (q2 / τ) := by ring
        _ ≤ _ := h'
    exact (div_le_iff₀ hτ).mp this
  have hbound : f z0 ≤ ζ ^ τ := by
    set w := Real.exp 1 / ζ with hw
    have hwpos : 0 < w := by positivity
    have hle : f z0 ≤ f w := hmin0 (show w ∈ Set.Ioi (0:ℝ) from hwpos)
    refine hle.trans ?_
    rw [hf w hwpos, Real.rpow_def_of_pos hζ]
    apply Real.exp_le_exp.mpr
    have hlw : Real.log w = 1 - Real.log ζ := by
      rw [hw, Real.log_div (Real.exp_pos 1).ne' hζ.ne', Real.log_exp]
    rw [hlw]
    have hs2 : (1.4 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    -- q2 w^2 ≤ τ/16, q1 w ≤ τ/√2
    have hq2w : q2 * w ^ 2 ≤ τ / 16 := by
      rw [hw, div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith [hB]
    have hq1w : q1 * w ≤ τ * (5 / 7) := by
      rw [hw, ← mul_div_assoc, div_le_iff₀ hζ]
      have : Real.exp 1 * q1 * 1.4 ≤ Real.sqrt 2 * Real.exp 1 * q1 :=
        by nlinarith [mul_nonneg he.le hq1]
      nlinarith [hA, this]
    nlinarith [mul_nonneg hq1 hwpos.le, mul_pos hq2 hτ]
  -- any minimizer is z0
  refine ⟨⟨z0, hz0, hmin0⟩, ?_⟩
  intro z hz hzmin
  have hle : f z ≤ f z0 := hzmin (show z0 ∈ Set.Ioi (0:ℝ) from hz0)
  rw [hf z hz, hf z0 hz0] at hle
  have hle' := Real.exp_le_exp.mp hle
  have hsq : q2 * (z - z0) ^ 2 ≤ 0 := by linarith [key z hz]
  have hzz : z = z0 := by
    have : (z - z0) ^ 2 ≤ 0 := by
      by_contra h
      push_neg at h
      nlinarith [mul_pos hq2 h]
    have : z - z0 = 0 := by nlinarith [sq_nonneg (z - z0)]
    linarith
  subst hzz
  have hf0 : f z ≤ ζ ^ τ := hbound
  refine ⟨hf0, ?_, ?_⟩
  · field_simp
    nlinarith [hcrit]
  · apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg hq1 hz.le]
