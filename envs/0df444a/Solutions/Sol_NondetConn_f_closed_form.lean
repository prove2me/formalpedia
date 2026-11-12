-- Prove2me | solution 1 for NondetConn.f_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T16:40:38.495909+00:00
-- url     : https://prove2.me/submissions/561b5d8e-e8ca-414c-9fcd-fa102f860e49

import Mathlib

set_option autoImplicit false

/-- Zhang's closed form `f_n = 4n/5`: summing the nested products telescopes by induction. -/
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc i n, (4 * (j : ℝ)) / (4 * j + 1) = 4 * n / 5 := by
  classical
  suffices h : ∀ n : ℕ,
      ∑ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc i n, (4 * (j : ℝ)) / (4 * j + 1) = 4 * n / 5 from
    h n
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : (n + 1) ∉ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc]
      omega
    rw [hsplit, Finset.sum_insert hnot]
    simp only [Finset.Icc_self, Finset.prod_singleton]
    have hprod : ∀ i ∈ Finset.Icc 1 n,
        ∏ j ∈ Finset.Icc i (n + 1), (4 * (j : ℝ)) / (4 * j + 1)
          = (∏ j ∈ Finset.Icc i n, (4 * (j : ℝ)) / (4 * j + 1)) *
              (4 * ((n + 1 : ℕ) : ℝ) / (4 * ((n + 1 : ℕ) : ℝ) + 1)) := by
      intro i hi
      have hin : i ≤ n := by
        simp only [Finset.mem_Icc] at hi
        omega
      have h := Finset.prod_Icc_succ_top (a := i) (b := n) (f := fun j : ℕ =>
        (4 * (j : ℝ)) / (4 * j + 1)) (by omega)
      simpa using h
    rw [Finset.sum_congr rfl hprod, ← Finset.sum_mul, ih]
    have hden : (4 * ((n + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
