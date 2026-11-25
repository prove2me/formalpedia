-- Prove2me | solution 2 for Menger.isEdgeConnected_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:57:31.259438+00:00
-- url     : https://prove2.me/submissions/1ca368ce-27aa-40f8-8949-3f384a03b5ea

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
public import Definitions.Def_MengerHamilton_Menger
public import Theorems.Thm_Menger_isEdgeReachable_iff

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger
variable {V : Type*}
namespace Menger
theorem _root_.solution [Finite V] (G : SimpleGraph V) (k : ℕ) :
    G.IsEdgeConnected k ↔
      ∀ u v : V, ∃ p : Fin k → G.Walk u v, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → (p i).edges.Disjoint (p j).edges := by
  exact ⟨fun h u v => (isEdgeReachable_iff G k u v).1 (h u v),
    fun h u v => (isEdgeReachable_iff G k u v).2 (h u v)⟩
end Menger
