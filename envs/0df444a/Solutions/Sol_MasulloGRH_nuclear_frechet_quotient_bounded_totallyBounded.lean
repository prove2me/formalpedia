-- Prove2me | solution 1 for MasulloGRH.nuclear_frechet_quotient_bounded_totallyBounded
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:02:58.868628+00:00
-- url     : https://prove2.me/submissions/b0adad3d-c692-471c-a700-b9eabc3830eb

import Theorems.Thm_MasulloGRH_nuclear_bounded_precompact
import Theorems.Thm_MasulloGRH_nuclear_quotient

set_option autoImplicit false

open Pointwise MasulloGRH

theorem solution (X : Type*) [AddCommGroup X]
    [Module ℂ X] [TopologicalSpace X] (hF : IsFrechet X) (hN : IsNuclear X)
    (W : Submodule ℂ X) (hW : IsClosed (W : Set X)) (B : Set (X ⧸ W))
    (hB : Bornology.IsVonNBounded ℂ B) :
    ∀ U ∈ nhds (0 : X ⧸ W), ∃ t : Finset (X ⧸ W), B ⊆ (t : Set (X ⧸ W)) + U := by
  intro U hU
  obtain ⟨t, ht⟩ := nuclear_bounded_precompact (X ⧸ W) (nuclear_quotient X hN W hW) B hB U hU
  refine ⟨t, fun y hy => ?_⟩
  have := ht hy
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
  obtain ⟨x, hx, hxy⟩ := this
  exact Set.mem_add.2 ⟨x, by simpa using hx, y - x, hxy, by abel⟩
