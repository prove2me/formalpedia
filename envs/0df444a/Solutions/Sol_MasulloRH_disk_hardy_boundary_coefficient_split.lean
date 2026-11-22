-- Prove2me | solution 1 for MasulloRH.disk_hardy_boundary_coefficient_split
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T12:24:45.459313+00:00
-- url     : https://prove2.me/submissions/893d7c45-4e62-4084-bef9-7d011eae32c5

import Mathlib
open Finset
theorem solution (a : ℕ → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hcoeff : ∀ k, ‖a k‖ ≤ D * 2^k)
    (energy : ∀ N : ℕ, (∑ k ∈ range N, ((k:ℝ)+1)^4 * ‖a k‖^2) ≤ 1)
    (M : ℕ) (hM : 0 < M) :
    Summable (fun k => ‖a k‖) ∧
      (∑' k, ‖a k‖) ≤ D * ((2:ℝ)^M-1) + Real.sqrt (1/(M:ℝ)^3) := by
  have hm : 0 < (M:ℝ) := by exact_mod_cast hM
  let W (k : ℕ) := ((k:ℝ)+1)^4 * ‖a k‖^2
  have he (n : ℕ) : (∑ j ∈ range n, W (M+j)) ≤ 1 := by
    have hh := energy (M+n)
    change (∑ k ∈ range (M+n), W k) ≤ 1 at hh
    rw [sum_range_add] at hh
    have hn : 0 ≤ ∑ k ∈ range M, W k := by dsimp [W]; positivity
    linarith
  have step (t : ℝ) (ht : 0 < t) : 1/(t+1)^4 ≤ 1/t^3 - 1/(t+1)^3 := by
    field_simp
    nlinarith only [show 0 ≤ t^4 by positivity, show 0 ≤ t^3 by positivity,
      show 0 ≤ t^2 by positivity,ht]
  have ht (n : ℕ) : (∑ j ∈ range n, 1/(((M+j:ℕ):ℝ)+1)^4) ≤
      1/(M:ℝ)^3 - 1/(((M+n:ℕ):ℝ))^3 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ]
      have h := step (((M+n:ℕ):ℝ)) (by positivity)
      push_cast at *
      simp only [← add_assoc] at *
      linarith
  have tail (n : ℕ) : (∑ j ∈ range n, ‖a (M+j)‖) ≤ Real.sqrt (1/(M:ℝ)^3) := by
    have hh := sum_sq_le_sum_mul_sum_of_sq_le_mul (range n)
      (r := fun j => ‖a (M+j)‖)
      (f := fun j => W (M+j))
      (g := fun j => 1 / (((M+j:ℕ):ℝ)+1)^4)
      (fun j _ => by dsimp [W]; positivity) (fun j _ => by positivity)
      (fun j _ => by dsimp [W]; have hz : 0 < ((M+j:ℕ):ℝ)+1 := by positivity
                     field_simp <;> rfl)
    have hss : (∑ j ∈ range n, 1/(((M+j:ℕ):ℝ)+1)^4) ≤ 1/(M:ℝ)^3 :=
      (ht n).trans (sub_le_self _ (by positivity))
    have hsmall := (mul_le_mul_of_nonneg_right (he n)
      (show 0 ≤ ∑ j ∈ range n, 1/(((M+j:ℕ):ℝ)+1)^4 by positivity)).trans
      (by simpa using hss : (1:ℝ) * _ ≤ _)
    apply Real.le_sqrt_of_sq_le
    exact hh.trans (by simpa only [one_div] using hsmall)
  have low : (∑ k ∈ range M, ‖a k‖) ≤ D*((2:ℝ)^M-1) := by
    calc
      _ ≤ ∑ k ∈ range M, D*2^k := sum_le_sum (fun k _ => hcoeff k)
      _ = _ := by
        rw [← mul_sum]
        congr 1
        have h := geom_sum_mul (2:ℝ) M
        norm_num at h ⊢
        exact h
  have bound (n : ℕ) : (∑ j ∈ range n, ‖a j‖) ≤
      D*((2:ℝ)^M-1)+Real.sqrt (1/(M:ℝ)^3) := by
    calc
      _ ≤ ∑ j ∈ range (M+n), ‖a j‖ := sum_le_sum_of_subset_of_nonneg
        (range_mono (by omega)) (fun _ _ _ => norm_nonneg _)
      _ ≤ _ := by rw [sum_range_add]; exact add_le_add low (tail n)
  exact ⟨summable_of_sum_range_le (fun _ => norm_nonneg _) bound,
    Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _) bound⟩
