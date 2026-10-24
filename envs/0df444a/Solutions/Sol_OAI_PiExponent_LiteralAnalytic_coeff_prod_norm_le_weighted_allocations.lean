-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.coeff_prod_norm_le_weighted_allocations
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:45:22.031897+00:00
-- url     : https://prove2.me/submissions/bd1eb504-cce6-4a3c-8ad8-46b0c314d0b4

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
open scoped BigOperators

private theorem finite_convolution {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → PowerSeries ℂ) (B : σ → ℕ → ℝ) (k : ℕ)
    (hf : ∀ i n, ‖PowerSeries.coeff n (f i)‖ ≤ B i n) :
    ‖PowerSeries.coeff k (∏ i, f i)‖ ≤
      ∑ n : σ → Fin (k + 1), if ∑ i, (n i : ℕ) = k then ∏ i, B i (n i) else 0 := by
  classical
  have hb (i : σ) (n : ℕ) : 0 ≤ B i n := (norm_nonneg _).trans (hf i n)
  have hle (l : σ →₀ ℕ) (hl : l ∈ Finset.finsuppAntidiag Finset.univ k) (i : σ) : l i ≤ k := by
    have hsum := (Finset.mem_finsuppAntidiag.mp hl).1
    have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset σ)) => Nat.zero_le (l j))
      (Finset.mem_univ i)
    exact hi.trans_eq hsum
  have hreindex :
      (∑ l ∈ Finset.finsuppAntidiag Finset.univ k, ∏ i : σ, B i (l i)) =
      ∑ n : σ → Fin (k + 1), if ∑ i, (n i : ℕ) = k then ∏ i, B i (n i) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun l hl i => (⟨l i, Nat.lt_succ_of_le (hle l hl i)⟩ : Fin (k + 1))) ?_ ?_ ?_ ?_
    · intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.mem_finsuppAntidiag.mp hl).1
    · intro l hl m hm heq
      apply Finsupp.ext
      intro i
      exact congrArg Fin.val (congrFun heq i)
    · intro n hn
      have hs : (∑ i : σ, (n i : ℕ)) = k := (Finset.mem_filter.mp hn).2
      let l : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (n i : ℕ))
      have hl : l ∈ Finset.finsuppAntidiag Finset.univ k := by
        apply Finset.mem_finsuppAntidiag.mpr
        exact ⟨by simpa [l] using hs, Finset.subset_univ _⟩
      refine ⟨l, hl, ?_⟩
      funext i
      apply Fin.ext
      simp [l]
    · intro l hl
      rfl
  rw [show (∏ i, f i) = ∏ i ∈ (Finset.univ : Finset σ), f i by simp,
    PowerSeries.coeff_prod]
  calc
    _ ≤ ∑ l ∈ Finset.finsuppAntidiag Finset.univ k,
          ‖∏ i ∈ (Finset.univ : Finset σ), PowerSeries.coeff (l i) (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ Finset.finsuppAntidiag Finset.univ k, ∏ i : σ, B i (l i) := by
      apply Finset.sum_le_sum
      intro l hl
      simp only [norm_prod]
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hf i (l i))
    _ = _ := hreindex

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → PowerSeries ℂ) (e : σ → ℕ) (A : σ → ℝ) (k : ℕ)
    (hA : ∀ i, 0 ≤ A i)
    (hf : ∀ i n,
      ‖PowerSeries.coeff n (f i)‖ ≤
        A i *
          (if e i = 0 then (if n = 0 then (1 : ℝ) else 0)
           else (Nat.choose (n + e i - 1) n : ℝ))) :
    ‖PowerSeries.coeff k (∏ i, f i)‖ ≤
      ∑ n : σ → Fin (k + 1),
        (if ∑ i, (n i : ℕ) = k then
          ∏ i, (A i *
            (if e i = 0 then (if (n i : ℕ) = 0 then (1 : ℝ) else 0)
             else (Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ) : ℝ)))
         else 0) := by
  exact finite_convolution f
    (fun i n => A i * (if e i = 0 then (if n = 0 then (1 : ℝ) else 0)
      else (Nat.choose (n + e i - 1) n : ℝ))) k hf

#print axioms solution
