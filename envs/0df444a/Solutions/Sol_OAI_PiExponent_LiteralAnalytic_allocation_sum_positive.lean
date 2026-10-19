-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.allocation_sum_positive
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:53:32.679596+00:00
-- url     : https://prove2.me/submissions/722c4272-e709-4366-b382-e395c6a35429
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Definitions.Def_allocationSum
import Definitions.Def_weakCompositionFiber
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocationSum_eq_weakCompositionFiber_card
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_weakCompositionFiber_card

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) (he : ∀ i, 0 < e i) :
    OAI.PiExponent.LiteralAnalytic.allocationSum e k =
      (if ∑ i, e i = 0 then (if k = 0 then 1 else 0)
       else Nat.choose (k + (∑ i, e i) - 1) k) := by
  rw [OAI.PiExponent.LiteralAnalytic.allocationSum_eq_weakCompositionFiber_card]
  rw [OAI.PiExponent.LiteralAnalytic.weakCompositionFiber_card]
  have hcard : Fintype.card (Σ i : σ, Fin (e i)) = ∑ i, e i := by simp
  rw [hcard]
  by_cases hE : ∑ i, e i = 0
  · by_cases hk : k = 0
    · simp [hE, hk]
    · have hlt : k - 1 < k := by omega
      simp [hE, hk, Nat.choose_eq_zero_of_lt hlt]
  · simp [hE]
