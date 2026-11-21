-- Prove2me | solution 2 for MasulloGRH.nuclear_frechet_quotient_bounded_totallyBounded
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:03:59.828862+00:00
-- url     : https://prove2.me/submissions/654c96b6-43fc-41ea-8b25-c8e2450bce0a

import Theorems.Thm_MasulloGRH_nuclear_quotient
import Theorems.Thm_MasulloGRH_nuclear_bounded_precompact

set_option autoImplicit false

open MasulloGRH Set Pointwise

theorem solution (X : Type*) [AddCommGroup X]
    [Module ℂ X] [TopologicalSpace X] (hF : IsFrechet X) (hN : IsNuclear X)
    (W : Submodule ℂ X) (hW : IsClosed (W : Set X)) (B : Set (X ⧸ W))
    (hB : Bornology.IsVonNBounded ℂ B) :
    ∀ U ∈ nhds (0 : X ⧸ W), ∃ t : Finset (X ⧸ W), B ⊆ (t : Set (X ⧸ W)) + U := by
  intro U hU
  -- the quotient of a nuclear space by a closed subspace is nuclear
  have hQ : IsNuclear (X ⧸ W) := nuclear_quotient X hN W hW
  -- bounded subsets of a nuclear space are precompact
  obtain ⟨t, ht⟩ := nuclear_bounded_precompact (X ⧸ W) hQ B hB U hU
  refine ⟨t, fun y hy => ?_⟩
  obtain ⟨x, hx⟩ := mem_iUnion.1 (ht hy)
  obtain ⟨hxt, hyx⟩ := mem_iUnion.1 hx
  exact ⟨x, hxt, y - x, hyx, add_sub_cancel x y⟩
