-- Prove2me | solution 1 for OAI.Barnette.Network.faces_vertex_deleted_connected
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:32:50.222267+00:00
-- url     : https://prove2.me/submissions/f52a042c-38cb-4e47-aebc-7cdbbceea565

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Bonds.lean:L266-L303
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.faces_vertex_deleted_connected. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Theorems.Thm_OAI_Barnette_Network_Triangle_corner_iff_incident

-- ---- from OAI.Combinatorics.Hamiltonian.Bonds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Cycle flows, minimal cuts, and connected shores. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype E] [Fintype F] in
lemma Triangle.corner_avoiding {s : Finset E} (t : D.Triangle s) (z : F) :
    ∃ w, w ∈ Set.range t.corner ∧ w ≠ z := by
  by_cases h : t.corner 0 = z
  · refine ⟨t.corner 1,⟨1,rfl⟩,?_⟩
    intro hh
    have hi := t.corner_injective (h.trans hh.symm)
    norm_num at hi
  · exact ⟨t.corner 0,⟨0,rfl⟩,h⟩

omit [Fintype E] [Fintype F] in
lemma Triangle.reachable_avoiding {s : Finset E} (t : D.Triangle s) (z : F)
    {v w : F} (hv : v ∈ Set.range t.corner) (hw : w ∈ Set.range t.corner)
    (hvz : v ≠ z) (hwz : w ≠ z) :
    (D.graph.induce {v | v ≠ z}).Reachable ⟨v,hvz⟩ ⟨w,hwz⟩ := by
  obtain ⟨i,rfl⟩ := hv
  obtain ⟨j,rfl⟩ := hw
  by_cases hij : i = j
  · subst j; exact SimpleGraph.Reachable.refl _
  · exact (show (D.graph.induce {v | v ≠ z}).Adj ⟨t.corner i,hvz⟩ ⟨t.corner j,hwz⟩ from
      t.clique D hij).reachable

omit [Fintype V] [Fintype F] in

theorem faces_vertex_deleted_connected (hN : N.graph.Connected) (hD : D.graph.Connected)
    (sD : D.Simple) (face : ∀ v, D.Triangle (N.star v)) (z : F) :
    (D.graph.induce {v | v ≠ z}).Connected := by
  obtain ⟨v₀⟩ := hN.nonempty
  let : Nontrivial F := ⟨⟨(face v₀).corner 0,(face v₀).corner 1,by
    intro he; have hi := (face v₀).corner_injective he; norm_num at hi⟩⟩
  let H := D.graph.induce {v | v ≠ z}
  choose anchor ha hz using fun v => (face v).corner_avoiding D z
  let a (v : V) : {w : F | w ≠ z} := ⟨anchor v,hz v⟩
  have in_face (v : V) (e : E) (he : N.Incident e v) (w : F) (hw : D.Incident e w) :
      w ∈ Set.range (face v).corner :=
    ((face v).corner_iff_incident D w).mpr ⟨e,(N.mem_star e v).mpr he,hw⟩
  have step {v w : V} (hvw : N.graph.Adj v w) : H.Reachable (a v) (a w) := by
    obtain ⟨_,e,he⟩ := hvw
    have hv : N.Incident e v := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
    have hw : N.Incident e w := he.elim (fun h => Or.inr h.2) (fun h => Or.inl h.1)
    obtain ⟨u,hu,huz⟩ : ∃ u, D.Incident e u ∧ u ≠ z := by
      by_cases ht : D.tail e = z
      · exact ⟨D.head e,Or.inr rfl,fun hh => sD.loopless e (ht.trans hh.symm)⟩
      · exact ⟨D.tail e,Or.inl rfl,ht⟩
    have p := (face v).reachable_avoiding D z (ha v) (in_face v e hv u hu) (hz v) huz
    have q := (face w).reachable_avoiding D z (in_face w e hw u hu) (ha w) huz (hz w)
    exact p.trans q
  have all_faces {v w : V} : H.Reachable (a v) (a w) := by
    obtain ⟨p⟩ := hN v w
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons hvw p ih => exact (step hvw).trans ih
  apply (SimpleGraph.connected_iff_exists_forall_reachable H).mpr
  refine ⟨a v₀,?_⟩
  intro w
  obtain ⟨u,hu⟩ := hD.preconnected.exists_adj_of_nontrivial w.val
  obtain ⟨_,e,he⟩ := hu
  have hw : D.Incident e w.val := he.elim (fun he => Or.inl he.1) (fun he => Or.inr he.2)
  have hf := in_face (N.tail e) e (Or.inl rfl) w.val hw
  exact all_faces.trans ((face (N.tail e)).reachable_avoiding D z (ha _) hf (hz _) w.property)

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.faces_vertex_deleted_connected := @_root_.OAI.Barnette.Network.faces_vertex_deleted_connected
