-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.coeff_prod_norm_le_weighted_allocations_general
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:18:29.134305+00:00
-- url     : https://prove2.me/submissions/92586001-e9a5-47cd-bca0-fa84aca7c2f1

import Mathlib
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → PowerSeries ℂ) (B : σ → ℕ → ℝ) (k : ℕ)
    (hB : ∀ i n, 0 ≤ B i n)
    (hf : ∀ i n, ‖PowerSeries.coeff n (f i)‖ ≤ B i n) :
    ‖PowerSeries.coeff k (∏ i, f i)‖ ≤
      ∑ n : σ → Fin (k + 1),
        (if ∑ i, (n i : ℕ) = k then ∏ i, B i (n i : ℕ) else 0) := by
  rw [PowerSeries.coeff_prod, ← Finset.sum_filter]
  refine (norm_sum_le _ _).trans ?_
  have hle : ∀ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset σ) k, ∀ i, l i < k + 1 := by
    intro l hl i
    rw [Finset.mem_finsuppAntidiag] at hl
    have h1 := hl.1
    have := Finset.single_le_sum (f := ⇑l) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [h1] at this
    omega
  calc _ ≤ ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset σ) k, ∏ i, B i (l i) :=
        Finset.sum_le_sum (fun l _ => by
          rw [norm_prod]
          exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hf i _))
    _ = _ := by
        refine Finset.sum_bij' (fun l hl i => ⟨l i, hle l hl i⟩)
          (fun n _ => Finsupp.equivFunOnFinite.symm (fun i => (n i : ℕ))) ?_ ?_ ?_ ?_ ?_
        · intro l hl
          rw [Finset.mem_finsuppAntidiag] at hl
          simpa using hl.1
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
          simp [Finset.mem_finsuppAntidiag, hn]
        · intro l hl; ext i; simp
        · intro n hn; funext i; simp
        · intro l hl; rfl
