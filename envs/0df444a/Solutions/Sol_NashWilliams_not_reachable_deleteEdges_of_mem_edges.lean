-- Prove2me | solution 1 for NashWilliams.not_reachable_deleteEdges_of_mem_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:51:23.313796+00:00
-- url     : https://prove2.me/submissions/fb2bfcd1-951e-49b8-b973-f240f4ecdfd4

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
namespace NashWilliams
theorem _root_.solution {F : SimpleGraph V} (hF : F.IsAcyclic) {u v x y : V}
    (p : F.Walk u v) (hp : p.IsPath) (he : s(x, y) ∈ p.edges) :
    ¬ (F.deleteEdges {s(x, y)}).Reachable u v := by
  classical
  rintro ⟨q⟩
  have hq : (q.bypass.mapLe (deleteEdges_le _)).IsPath := (Walk.isPath_mapLe _).2 q.bypass_isPath
  have := (hF.subsingleton_path u v).elim ⟨p, hp⟩ ⟨_, hq⟩
  simp only [Subtype.mk.injEq] at this
  rw [this, Walk.edges_mapLe_eq_edges] at he
  have := q.bypass.edges_subset_edgeSet he
  simp [edgeSet_deleteEdges] at this
end NashWilliams
