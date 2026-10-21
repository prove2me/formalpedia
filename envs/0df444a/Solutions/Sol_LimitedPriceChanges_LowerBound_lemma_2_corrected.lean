-- Prove2me | solution 1 for LimitedPriceChanges.LowerBound.lemma_2_corrected
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:21:10.015051+00:00
-- url     : https://prove2.me/submissions/062f7fdc-a9d8-468b-ba08-e81f3e55e337

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_KL

set_option autoImplicit false
open LimitedPriceChanges.LowerBound

lemma log_lb (x : ℝ) (hx : 0 ≤ x) : x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  let g : ℝ → ℝ := fun x => Real.log (1 + x) - x + x ^ 2 / 2
  have hder : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt g (1 / (1 + x) - 1 + x) x := by
    intro x hx
    have h1 : (0 : ℝ) < 1 + x := by
      have : (0 : ℝ) ≤ x := hx
      linarith
    have := (((hasDerivAt_id' x).const_add 1).log h1.ne').sub (hasDerivAt_id' x)
    have h2 := this.add ((hasDerivAt_pow 2 x).div_const 2)
    refine h2.congr_deriv ?_
    simp
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x hx => (hder x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hder x (Set.mem_Ici.mpr (le_of_lt hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : (0 : ℝ) < x := hx
      rw [(hder x (Set.mem_Ici.mpr hx'.le)).deriv]
      have h1 : (0 : ℝ) < 1 + x := by linarith
      have : 1 / (1 + x) - 1 + x = x ^ 2 / (1 + x) := by field_simp; ring
      rw [this]; positivity
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp only [g] at this
  simp at this
  linarith

lemma kl_bound (a c : ℝ) (ha : 0 < a) (hac : a ≤ c) (hc : c < 1) :
    a * Real.log (a / c) + (1 - a) * Real.log ((1 - a) / (1 - c)) ≤
      (c - a) ^ 2 * (1 / (2 * a) + 1 / (1 - c)) := by
  have hc0 : 0 < c := lt_of_lt_of_le ha hac
  have h1c : 0 < 1 - c := by linarith
  have h1a : 0 < 1 - a := by linarith
  have hu : 0 ≤ (c - a) / a := div_nonneg (by linarith) ha.le
  have e1 : Real.log (a / c) = - Real.log (1 + (c - a) / a) := by
    have : 1 + (c - a) / a = c / a := by field_simp; ring
    rw [this, ← Real.log_inv, inv_div]
  have b1 := log_lb _ hu
  have t1 : a * Real.log (a / c) ≤ -(c - a) + (c - a) ^ 2 / (2 * a) := by
    rw [e1]
    have : a * (-Real.log (1 + (c - a) / a)) ≤ a * (-((c - a) / a - ((c - a) / a) ^ 2 / 2)) := by
      apply mul_le_mul_of_nonneg_left _ ha.le
      linarith
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  have t2 : (1 - a) * Real.log ((1 - a) / (1 - c)) ≤ (c - a) + (c - a) ^ 2 / (1 - c) := by
    have := Real.log_le_sub_one_of_pos (div_pos h1a h1c)
    have h3 : (1 - a) * Real.log ((1 - a) / (1 - c)) ≤ (1 - a) * ((1 - a) / (1 - c) - 1) :=
      mul_le_mul_of_nonneg_left this h1a.le
    refine h3.trans (le_of_eq ?_)
    field_simp
    ring
  have : (c - a) ^ 2 * (1 / (2 * a) + 1 / (1 - c)) = (c - a) ^ 2 / (2 * a) + (c - a) ^ 2 / (1 - c) := by
    field_simp
  rw [this]
  linarith

theorem solution (z z' p : ℝ)
    (hz : z ∈ Set.Icc (1 / 6 : ℝ) (5 / 6 : ℝ))
    (hz' : z' ∈ Set.Icc (1 / 6 : ℝ) (5 / 6 : ℝ))
    (hzz' : z' ≤ z) (hp : p ∈ Set.Icc (1 : ℝ) 6)
    (hinterior : p * z ≤ 11 / 6) :
    klBer (nu p z) (nu p z') ≤ 108 * (z - z') ^ 2 := by
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hz1', hz2'⟩ := hz'
  obtain ⟨hp1, hp2⟩ := hp
  have ha : nu p z = 1 - p * z / 2 := by
    unfold nu; rw [max_eq_right]; linarith
  have hc : nu p z' = 1 - p * z' / 2 := by
    unfold nu; rw [max_eq_right]; nlinarith
  unfold klBer
  rw [ha, hc]
  have ha0 : 1 / 12 ≤ 1 - p * z / 2 := by linarith
  have hac : 1 - p * z / 2 ≤ 1 - p * z' / 2 := by nlinarith
  have hc1 : p / 12 ≤ p * z' / 2 := by nlinarith
  have hc2 : 1 - p * z' / 2 < 1 := by nlinarith
  refine (kl_bound _ _ (by linarith) hac hc2).trans ?_
  have hsub : (1 - p * z' / 2) - (1 - p * z / 2) = p * (z - z') / 2 := by ring
  have hden : 1 - (1 - p * z' / 2) = p * z' / 2 := by ring
  rw [hsub, hden]
  have hk : 1 / (2 * (1 - p * z / 2)) + 1 / (p * z' / 2) ≤ 6 + 12 / p := by
    have h1 : 1 / (2 * (1 - p * z / 2)) ≤ 6 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have h2 : 1 / (p * z' / 2) ≤ 12 / p := by
      rw [div_le_div_iff₀ (by nlinarith) (by linarith)]; nlinarith
    linarith
  have hsq : 0 ≤ (p * (z - z') / 2) ^ 2 := sq_nonneg _
  calc (p * (z - z') / 2) ^ 2 * (1 / (2 * (1 - p * z / 2)) + 1 / (p * z' / 2))
      ≤ (p * (z - z') / 2) ^ 2 * (6 + 12 / p) := mul_le_mul_of_nonneg_left hk hsq
    _ = (z - z') ^ 2 * (3 * p ^ 2 / 2 + 3 * p) := by field_simp; ring
    _ ≤ (z - z') ^ 2 * 72 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); nlinarith
    _ ≤ 108 * (z - z') ^ 2 := by nlinarith [sq_nonneg (z - z')]
