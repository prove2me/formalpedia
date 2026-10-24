-- Prove2me | solution 1 for L0BnB.Duality.eq_45
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T07:49:39.923877+00:00
-- url     : https://prove2.me/submissions/2debb3d1-b058-4133-8246-ee8d66697942

import Mathlib
import Definitions.Def_L0BnB_Duality_Dual

set_option autoImplicit false
open L0BnB.Duality

namespace SparseDualitySupport

lemma sqrt_scaling (l0 l2 : ℝ) (h0 : 0 < l0) (h2 : 0 < l2) :
    Real.sqrt (l0 / l2) * Real.sqrt (l2 / l0) = 1 ∧
    l0 * Real.sqrt (l2 / l0) = Real.sqrt (l0 * l2) := by
  constructor
  · rw [← Real.sqrt_mul (div_pos h0 h2).le]
    have : l0 / l2 * (l2 / l0) = 1 := by field_simp
    rw [this, Real.sqrt_one]
  · have hs := Real.sq_sqrt (div_pos h2 h0).le
    have hw := Real.sq_sqrt (mul_pos h0 h2).le
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    have hx : l0 * Real.sqrt (l2 / l0) ^ 2 = l2 := by
      rw [hs]; field_simp
    nlinarith

lemma psi1_linear (l0 l2 b : ℝ) (h0 : 0 < l0) (h2 : 0 < l2)
    (hb : |b| ≤ Real.sqrt (l0 / l2)) :
    L0BnB.Reduced.psi1 l0 l2 b = 2 * Real.sqrt (l0 * l2) * |b| := by
  obtain ⟨ht, hw⟩ := sqrt_scaling l0 l2 h0 h2
  have hs := Real.sqrt_nonneg (l2 / l0)
  have hbound : |b * Real.sqrt (l2 / l0)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hs]
    calc |b| * Real.sqrt (l2 / l0) ≤ Real.sqrt (l0 / l2) * Real.sqrt (l2 / l0) :=
      mul_le_mul_of_nonneg_right hb hs
      _ = 1 := ht
  unfold L0BnB.Reduced.psi1 L0BnB.Reduced.reverseHuber
  rw [if_pos hbound, abs_mul, abs_of_nonneg hs]
  calc 2 * l0 * (|b| * Real.sqrt (l2 / l0)) = 2 * (l0 * Real.sqrt (l2 / l0)) * |b| := by ring
    _ = _ := by rw [hw]

lemma interval_linear_minimum (c a t : ℝ) (hc : 0 ≤ c) (ht : 0 ≤ t) :
    let u := if 0 ≤ c - |a| then 0 else -t * Real.sign a
    u ∈ Set.Icc (-t) t ∧ ∀ b ∈ Set.Icc (-t) t,
      c * |u| + a * u ≤ c * |b| + a * b := by
  dsimp
  by_cases h : 0 ≤ c - |a|
  · rw [if_pos h]
    refine ⟨⟨by linarith, ht⟩, ?_⟩
    intro b hb
    have ha : -(|a| * |b|) ≤ a * b := by simpa only [abs_mul] using neg_abs_le (a*b)
    have hz := mul_nonneg h (abs_nonneg b)
    simp only [abs_zero, mul_zero, zero_add]
    nlinarith
  · rw [if_neg h]
    have hane : a ≠ 0 := by intro hz; subst a; simp at h; linarith
    have habs : |-t * Real.sign a| = t := by
      rcases lt_or_gt_of_ne hane with ha | ha
      · rw [Real.sign_of_neg ha]; simp [abs_of_nonneg ht]
      · rw [Real.sign_of_pos ha]; simp [abs_of_nonneg ht]
    have hau : a * (-t * Real.sign a) = -|a| * t := by
      rcases lt_or_gt_of_ne hane with ha | ha
      · rw [Real.sign_of_neg ha, abs_of_neg ha]; ring
      · rw [Real.sign_of_pos ha, abs_of_pos ha]; ring
    refine ⟨abs_le.mp (by rw [habs]), ?_⟩
    intro b hb
    have hbt : |b| ≤ t := abs_le.mpr hb
    have ha : -(|a| * |b|) ≤ a * b := by simpa only [abs_mul] using neg_abs_le (a*b)
    have hm := mul_le_mul_of_nonpos_left hbt (le_of_lt (not_le.mp h))
    rw [habs, hau]
    nlinarith

end SparseDualitySupport

theorem solution (lam0 lam2 a η : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hη : 0 ≤ η) :
    betaTilde45 lam0 lam2 a η ∈ Set.Icc (-Real.sqrt (lam0 / lam2)) (Real.sqrt (lam0 / lam2)) ∧
      ∀ b ∈ Set.Icc (-Real.sqrt (lam0 / lam2)) (Real.sqrt (lam0 / lam2)),
        D lam0 lam2 a η (betaTilde45 lam0 lam2 a η) ≤ D lam0 lam2 a η b := by
  have hc : 0 ≤ 2 * Real.sqrt (lam0 * lam2) + η := by positivity
  obtain ⟨hu, hmin⟩ := SparseDualitySupport.interval_linear_minimum
    (2 * Real.sqrt (lam0 * lam2) + η) a (Real.sqrt (lam0 / lam2)) hc (Real.sqrt_nonneg _)
  change betaTilde45 lam0 lam2 a η ∈ _ at hu
  change ∀ b ∈ Set.Icc (-Real.sqrt (lam0 / lam2)) (Real.sqrt (lam0 / lam2)),
    (2 * Real.sqrt (lam0 * lam2) + η) * |betaTilde45 lam0 lam2 a η| + a * betaTilde45 lam0 lam2 a η ≤
      (2 * Real.sqrt (lam0 * lam2) + η) * |b| + a * b at hmin
  refine ⟨hu, ?_⟩
  intro b hb
  unfold D
  rw [SparseDualitySupport.psi1_linear _ _ _ hlam0 hlam2 (abs_le.mpr hu),
    SparseDualitySupport.psi1_linear _ _ _ hlam0 hlam2 (abs_le.mpr hb)]
  nlinarith [hmin b hb]
