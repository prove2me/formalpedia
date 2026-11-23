-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.addSubgroupIndependenceNumber_ge_card_of_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:06.569042+00:00
-- url     : https://prove2.me/submissions/83c69a9b-385e-4590-890e-f2296c3dfa9b

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution {G : Type*} [AddGroup G] [Fintype G]
    (Γ : SimpleGraph G) (H : AddSubgroup G) (hH : Γ.IsIndepSet (H : Set G)) :
    addSubgroupIndependenceNumber Γ ≥ Nat.card H := by
  -- H is in the set { n | ∃ H, Γ.IsIndepSet H ∧ Nat.card H = n } with value Nat.card H
  -- The sSup of this set is ≥ Nat.card H
  simp only [addSubgroupIndependenceNumber]
  apply le_csSup
  · -- BddAbove: The set of cardinalities is bounded by |G|
    use Fintype.card G
    intro x ⟨H', _, hcard⟩
    rw [← hcard]
    haveI : Fintype H' := Fintype.ofFinite H'
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  · -- H is in the set with card = Nat.card H
    exact ⟨H, hH, rfl⟩
end GroupTheoreticShannonCapacity
