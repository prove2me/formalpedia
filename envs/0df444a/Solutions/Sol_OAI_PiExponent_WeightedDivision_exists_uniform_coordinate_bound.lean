-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.exists_uniform_coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:16:29.067718+00:00
-- url     : https://prove2.me/submissions/d2b9ff1d-ed15-4837-be87-2fc214f5ce7a

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) (B : ℝ) :
    ∃ N : ℕ, ∀ u : ι →₀ ℕ,
      (∑ i, d i * (u i : ℝ)) ≤ B → ∀ i, u i ≤ N := by
  classical
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    obtain ⟨j, hj, hmin⟩ :=
      Finset.exists_min_image Finset.univ d ⟨i₀, Finset.mem_univ _⟩
    let δ : ℝ := d j
    have hδ : 0 < δ := hd j
    let N : ℕ := Nat.ceil (B / δ)
    have hN : B / δ ≤ (N : ℝ) := Nat.le_ceil _
    refine ⟨N, fun u hu i => ?_⟩
    have hterm_nonneg (k : ι) : 0 ≤ d k * (u k : ℝ) :=
      mul_nonneg (le_of_lt (hd k)) (Nat.cast_nonneg (u k))
    have hterm_le : d i * (u i : ℝ) ≤ ∑ k, d k * (u k : ℝ) :=
      Finset.single_le_sum (fun k hk => hterm_nonneg k) (Finset.mem_univ i)
    have hδterm : δ * (u i : ℝ) ≤ B := by
      calc
        δ * (u i : ℝ) ≤ d i * (u i : ℝ) :=
          mul_le_mul_of_nonneg_right (hmin i (Finset.mem_univ i))
            (Nat.cast_nonneg (u i))
        _ ≤ ∑ k, d k * (u k : ℝ) := hterm_le
        _ ≤ B := hu
    have hratio : (u i : ℝ) ≤ B / δ :=
      (le_div_iff₀ hδ).2 (by simpa only [mul_comm] using hδterm)
    exact Nat.cast_le.mp (hratio.trans hN)
  · refine ⟨0, fun u hu i => ?_⟩
    exact (hι ⟨i⟩).elim
