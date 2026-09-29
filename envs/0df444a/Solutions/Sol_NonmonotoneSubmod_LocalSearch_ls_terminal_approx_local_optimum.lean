-- Prove2me | solution 1 for NonmonotoneSubmod.LocalSearch.ls_terminal_approx_local_optimum
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:27:10.336495+00:00
-- url     : https://prove2.me/submissions/e8c35e3c-36fc-44fb-837f-3f81d4ae6154

import Mathlib
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsApproxLocalOptimum
import Definitions.Def_NonmonotoneSubmod_LocalSearch_LSAlgorithm

namespace NonmonotoneSubmod.LocalSearch

theorem aux_lsterm_add {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ)
    (f : Finset X → ℝ) (S : Finset X) (hS : IsLSTerminal ε f S) :
    ∀ a, a ∉ S → f (insert a S) ≤ lsFactor X ε * f S := by
  intro a ha
  by_contra h
  exact hS (insert a S) (Or.inl ⟨a, ha, not_le.mp h, rfl⟩)

end NonmonotoneSubmod.LocalSearch

open NonmonotoneSubmod.LocalSearch

theorem solution {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ)
    (f : Finset X → ℝ) (S : Finset X) (hS : IsLSTerminal ε f S) :
    IsApproxLocalOptimum f (ε / (Fintype.card X : ℝ) ^ 2) S := by
  have hadd := aux_lsterm_add ε f S hS
  refine ⟨?_, ?_⟩
  · intro v hv
    by_contra h
    exact hS (S.erase v) (Or.inr ⟨hadd, v, hv, not_le.mp h, rfl⟩)
  · intro v hv
    exact hadd v hv
