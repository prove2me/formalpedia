-- Prove2me | solution 1 for HiringLP.SimLower.proposition_EC_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:01:27.535766+00:00
-- url     : https://prove2.me/submissions/e6019e65-a933-46a8-bbff-becd40389798

import Mathlib
import Definitions.Def_HiringLP_SimLower_PoissonRatio

set_option autoImplicit false
open HiringLP.SimLower Finset

theorem pois_hasSum_HSL2 (l : ℝ) :
    HasSum (fun j : ℕ => Real.exp (-l) * l ^ j / (j.factorial : ℝ)) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) l).mul_left (Real.exp (-l))
  rw [← Real.exp_eq_exp_ℝ] at h
  have e : Real.exp (-l) * Real.exp l = 1 := by rw [← Real.exp_add]; simp
  rw [e] at h
  have e2 : (fun j : ℕ => Real.exp (-l) * l ^ j / (j.factorial : ℝ)) =
      fun j : ℕ => Real.exp (-l) * (l ^ j / (j.factorial : ℝ)) := by
    funext j; ring
  rw [e2]; exact h

theorem pois_rec_HSL2 (l : ℝ) (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) * (Real.exp (-l) * l ^ (m + 1) / ((m + 1).factorial : ℝ)) =
      l * (Real.exp (-l) * l ^ m / (m.factorial : ℝ)) := by
  rw [Nat.factorial_succ]
  push_cast
  have : ((m.factorial : ℝ)) ≠ 0 := by positivity
  have : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem pois_partial_HSL2 (l : ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), (i : ℝ) * (Real.exp (-l) * l ^ i / (i.factorial : ℝ)) =
      l * ∑ i ∈ range m, (Real.exp (-l) * l ^ i / (i.factorial : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ _ m, pois_rec_HSL2 l m]
    ring

theorem solution (k : ℕ) :
    expMinPois k k = k * (1 - Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / (k.factorial : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [expMinPois]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set l : ℝ := ((m + 1 : ℕ) : ℝ) with hl
  set p : ℕ → ℝ := fun j => Real.exp (-l) * l ^ j / (j.factorial : ℝ) with hp
  have hP : HasSum p 1 := pois_hasSum_HSL2 l
  have hP2 : HasSum (fun n => p (n + (m + 1))) (1 - ∑ i ∈ range (m + 1), p i) :=
    (hasSum_nat_add_iff' (m + 1)).2 hP
  have hF : HasSum (fun n : ℕ => min ((n + (m + 1) : ℕ) : ℝ) ((m + 1 : ℕ) : ℝ) * p (n + (m + 1)))
      (l * (1 - ∑ i ∈ range (m + 1), p i)) := by
    have e : (fun n : ℕ => min ((n + (m + 1) : ℕ) : ℝ) ((m + 1 : ℕ) : ℝ) * p (n + (m + 1))) =
        fun n : ℕ => l * p (n + (m + 1)) := by
      funext n
      have : min ((n + (m + 1) : ℕ) : ℝ) ((m + 1 : ℕ) : ℝ) = l := by
        rw [hl]; apply min_eq_right; exact_mod_cast Nat.le_add_left _ _
      rw [this]
    rw [e]; exact hP2.mul_left l
  have hF2 : HasSum (fun j : ℕ => min (j : ℝ) ((m + 1 : ℕ) : ℝ) * p j)
      (l * (1 - ∑ i ∈ range (m + 1), p i) +
        ∑ i ∈ range (m + 1), min (i : ℝ) ((m + 1 : ℕ) : ℝ) * p i) := by
    have := (hasSum_nat_add_iff' (f := fun j : ℕ => min (j : ℝ) ((m + 1 : ℕ) : ℝ) * p j) (m + 1)).1
      (by
        have e3 : l * (1 - ∑ i ∈ range (m + 1), p i) +
            ∑ i ∈ range (m + 1), min (i : ℝ) ((m + 1 : ℕ) : ℝ) * p i -
            ∑ i ∈ range (m + 1), min (i : ℝ) ((m + 1 : ℕ) : ℝ) * p i =
            l * (1 - ∑ i ∈ range (m + 1), p i) := by ring
        rw [e3]; exact hF)
    exact this
  unfold expMinPois
  rw [hF2.tsum_eq]
  have hmin : ∑ i ∈ range (m + 1), min (i : ℝ) ((m + 1 : ℕ) : ℝ) * p i =
      ∑ i ∈ range (m + 1), (i : ℝ) * p i := by
    apply sum_congr rfl
    intro i hi
    have : (i : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      have := mem_range.1 hi
      exact_mod_cast this.le
    rw [min_eq_left this]
  rw [hmin, hp]
  simp only []
  rw [pois_partial_HSL2 l m]
  have hpm : Real.exp (-l) * l ^ (m + 1) / ((m + 1).factorial : ℝ) =
      Real.exp (-l) * l ^ m / (m.factorial : ℝ) := by
    have h := pois_rec_HSL2 l m
    have hne : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have : ((m + 1 : ℕ) : ℝ) = l := rfl
    rw [this] at h
    have hl0 : l ≠ 0 := by rw [← this]; exact hne
    exact mul_left_cancel₀ hl0 h
  rw [sum_range_succ, hpm]
  ring
