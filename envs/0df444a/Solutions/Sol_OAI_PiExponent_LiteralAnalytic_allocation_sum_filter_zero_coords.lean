-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.allocation_sum_filter_zero_coords
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:17:27.99999+00:00
-- url     : https://prove2.me/submissions/505b1396-f68e-4ced-85ef-5a3c4c2fd7c0

import Mathlib.Tactic
import Definitions.Def_allocationSum
import Definitions.Def_allocationWeight

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    OAI.PiExponent.LiteralAnalytic.allocationSum e k =
      ∑ n : {n : σ → Fin (k + 1) // ∀ i, e i = 0 → n i = 0},
        OAI.PiExponent.LiteralAnalytic.allocationWeight e k n.1 := by
  classical
  unfold OAI.PiExponent.LiteralAnalytic.allocationSum
  have hw : ∀ n : σ → Fin (k + 1),
      (if ∑ i, (n i : ℕ) = k then
        ∏ i, (if e i = 0 then (if (n i : ℕ) = 0 then 1 else 0)
          else Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ))
       else 0) = OAI.PiExponent.LiteralAnalytic.allocationWeight e k n := by
    intro n; rfl
  simp_rw [hw]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun n : σ → Fin (k + 1) => ∀ i, e i = 0 → n i = 0))
    (p := fun n : σ → Fin (k + 1) => ∀ i, e i = 0 → n i = 0) (by intro n; simp)]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n _ hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hn
  obtain ⟨i, hi0, hi⟩ := hn
  unfold OAI.PiExponent.LiteralAnalytic.allocationWeight
  split_ifs with hs
  · apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [if_pos hi0, if_neg]
    intro h
    exact hi (Fin.ext h)
  · rfl
