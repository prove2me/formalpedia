-- Prove2me | solution 1 for MasulloRH.lift_mellin_jet_matrix_entry
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:37:24.29981+00:00
-- url     : https://prove2.me/submissions/46f1dcce-48d9-4b61-885c-f363d36cf67a

import Mathlib

open MeasureTheory

theorem solution (φ G : ℝ → ℂ) (s : ℂ) (m j : ℕ)
    (hi : ∀ d ≤ m, Integrable (fun x : ℝ => G x * (x:ℂ)^d * Complex.exp (s*x)))
    (hb : ∀ d ≤ m, (∫ x : ℝ, G x * (x:ℂ)^d * Complex.exp (s*x)) =
      if d = j then 1 else 0) :
    (∫ y : ℝ, φ (Real.exp y) * ∫ x : ℝ,
      G x * ((x:ℂ)+y)^m * Complex.exp (s*((x:ℂ)+y))) =
      if j ≤ m then (m.choose j : ℂ) * ∫ y : ℝ,
        φ (Real.exp y) * (y:ℂ)^(m-j) * Complex.exp (s*y) else 0 := by
  classical
  let c := fun (y : ℝ) (d : ℕ) => (m.choose d : ℂ) * (y:ℂ)^(m-d) * Complex.exp (s*y)
  have hrow (y : ℝ) : (∫ x : ℝ, G x * ((x:ℂ)+y)^m * Complex.exp (s*((x:ℂ)+y))) =
      if j ≤ m then c y j else 0 := by
    have h (x : ℝ) : G x * ((x:ℂ)+y)^m * Complex.exp (s*((x:ℂ)+y)) =
        ∑ d ∈ Finset.range (m+1), c y d * (G x * (x:ℂ)^d * Complex.exp (s*x)) := by
      rw [add_pow, mul_add, Complex.exp_add, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      dsimp [c]
      ring
    simp_rw [h]
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul]
      calc
        _ = ∑ d ∈ Finset.range (m+1), if d = j then c y d else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [hb d (by simpa using hd)]
          split <;> simp_all
        _ = _ := by simp
    · intro d hd
      exact (hi d (by simpa using hd)).const_mul _
  simp_rw [hrow]
  split_ifs with hj
  · rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    dsimp [c]
    ring
  · simp
