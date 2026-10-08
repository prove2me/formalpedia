-- Prove2me | solution 1 for NashBargainingProblem.Axiomatic.sum_le_two_of_one_one_max
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:27:09.862357+00:00
-- url     : https://prove2.me/submissions/3a19c97d-e25b-43eb-aa21-3790b5ee75b8

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NashWork

theorem sum_le_two_of_one_one_max (S : Set (ℝ × ℝ))
    (hS_convex : Convex ℝ S) (h11 : ((1 : ℝ), (1 : ℝ)) ∈ S)
    (hmax : ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s.1 * s.2 ≤ 1) :
    ∀ u ∈ S, u.1 + u.2 ≤ 2 := by
  intro u hu
  by_contra hcon
  push Not at hcon
  set a := u.1 - 1 with ha
  set b := u.2 - 1 with hb
  set c := a + b with hc
  have hcpos : 0 < c := by simp only [hc, ha, hb]; linarith
  set t : ℝ := min (1 / (|a| + |b| + 1)) (c / (2 * (|a * b| + 1))) with ht
  have hden : 0 < |a| + |b| + 1 := by positivity
  have hden2 : 0 < 2 * (|a * b| + 1) := by positivity
  have htpos : 0 < t := lt_min (by positivity) (by positivity)
  have ht1 : t ≤ 1 / (|a| + |b| + 1) := min_le_left _ _
  have ht2 : t ≤ c / (2 * (|a * b| + 1)) := min_le_right _ _
  have ht1' : t * (|a| + |b| + 1) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right ht1 hden.le
    rwa [one_div, inv_mul_cancel₀ hden.ne'] at this
  have ht2' : t * (2 * (|a * b| + 1)) ≤ c := by
    have := mul_le_mul_of_nonneg_right ht2 hden2.le
    rwa [div_mul_cancel₀ _ hden2.ne'] at this
  have htle1 : t ≤ 1 := by nlinarith [abs_nonneg a, abs_nonneg b]
  have hq : (1 - t) • ((1 : ℝ), (1 : ℝ)) + t • u ∈ S :=
    hS_convex h11 hu (by linarith) htpos.le (by ring)
  set q : ℝ × ℝ := (1 - t) • ((1 : ℝ), (1 : ℝ)) + t • u with hqdef
  have hqx : q.1 = 1 + t * a := by simp only [hqdef, Prod.fst_add, Prod.smul_fst, smul_eq_mul, ha]; ring
  have hqy : q.2 = 1 + t * b := by simp only [hqdef, Prod.snd_add, Prod.smul_snd, smul_eq_mul, hb]; ring
  have hta : t * |a| < 1 := by nlinarith [abs_nonneg a, abs_nonneg b]
  have htb : t * |b| < 1 := by nlinarith [abs_nonneg a, abs_nonneg b]
  have hx0 : 0 ≤ 1 + t * a := by nlinarith [neg_abs_le a, abs_nonneg a]
  have hy0 : 0 ≤ 1 + t * b := by nlinarith [neg_abs_le b, abs_nonneg b]
  have := hmax q hq (by rw [hqx]; exact hx0) (by rw [hqy]; exact hy0)
  rw [hqx, hqy] at this
  -- (1 + t a)(1 + t b) = 1 + t c + t² a b > 1
  have hab : -(|a * b|) ≤ a * b := neg_abs_le _
  nlinarith [abs_nonneg (a * b), mul_pos htpos htpos]

end NashWork

theorem solution (S : Set (ℝ × ℝ))
    (hS_convex : Convex ℝ S) (h11 : ((1 : ℝ), (1 : ℝ)) ∈ S)
    (hmax : ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s.1 * s.2 ≤ 1) :
    ∀ u ∈ S, u.1 + u.2 ≤ 2 :=
  NashWork.sum_le_two_of_one_one_max S hS_convex h11 hmax

#print axioms solution
