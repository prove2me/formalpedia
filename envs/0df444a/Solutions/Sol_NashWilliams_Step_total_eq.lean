-- Prove2me | solution 1 for NashWilliams.Step.total_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:51:55.614617+00:00
-- url     : https://prove2.me/submissions/41be824e-c0b6-410b-9368-b35a958332da

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Theorems.Thm_NashWilliams_total_update

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
variable (G : SimpleGraph V) {k : ℕ}
variable {G}
namespace NashWilliams
namespace Step
theorem _root_.solution [Finite V] {F F' : Fin k → SimpleGraph V} (h : Step G F F') :
    total F' = total F := by
  obtain ⟨i, u, v, x, y, huv, hxy, hac, rfl⟩ := h
  have h1 := total_update F i ((F i).deleteEdges {s(x, y)} ⊔ edge u v)
  have hne : u ≠ v := huv.1.ne
  have h2 : ((F i).deleteEdges {s(x, y)} ⊔ edge u v).edgeSet.ncard = (F i).edgeSet.ncard := by
    rw [edgeSet_sup, edgeSet_deleteEdges, edgeSet_edge_of_ne hne,
      Set.ncard_union_eq (Set.disjoint_singleton_right.2 fun h ↦ huv.2 i h.1) (Set.toFinite _)
        (Set.toFinite _), Set.ncard_singleton]
    exact Set.ncard_sdiff_singleton_add_one (show s(x, y) ∈ (F i).edgeSet from hxy)
      (Set.toFinite _)
  omega
end Step
end NashWilliams
