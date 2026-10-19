-- Prove2me | solution 1 for OAI.Barnette.Network.region_connected
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:35:39.335629+00:00
-- url     : https://prove2.me/submissions/94dc097f-1d10-4d0f-b885-66a5d8000463

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/DiskRegions.lean:L72-L151
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.region_connected. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Theorems.Thm_OAI_Barnette_Network_Triangle_corner_iff_incident

-- ---- from OAI.Combinatorics.Hamiltonian.DiskRegions ----
namespace OAI

/-! Connected face regions and the exact disk Euler formula. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in

lemma region_connected (A : Finset V) (hA : (N.graph.induce {v | v ∈ A}).Connected)
    (sD : D.Simple) (face : ∀ v, D.Triangle (N.star v)) :
    (N.region D A).graph.Connected := by
  let R := N.region D A
  have in_face {v : V} (hv : v ∈ A) {z : F} (hz : z ∈ Set.range (face v).corner) :
      z ∈ N.regionVertices D A := by
    obtain ⟨e,he,hz⟩ := ((face v).corner_iff_incident D z).mp hz
    have hv' := (N.mem_star e v).mp he
    have heA : e ∈ N.regionEdges A := by
      apply (N.mem_regionEdges A e).mpr
      exact hv'.elim (fun he => Or.inl (he ▸ hv)) (fun he => Or.inr (he ▸ hv))
    exact (N.mem_regionVertices D A z).mpr ⟨e,heA,hz⟩
  let a (v : {v // v ∈ A}) : N.regionVertices D A :=
    ⟨(face v.val).corner 0,in_face v.property ⟨0,rfl⟩⟩
  have local_path {v : V} (hv : v ∈ A) {z w : N.regionVertices D A}
      (hz : z.val ∈ Set.range (face v).corner) (hw : w.val ∈ Set.range (face v).corner) :
      R.graph.Reachable z w := by
    obtain ⟨i,hi⟩ := hz
    obtain ⟨j,hj⟩ := hw
    by_cases hij : i = j
    · have he : z = w := Subtype.ext (hi.symm.trans (hij ▸ hj))
      rw [he]
    · have hadj := (face v).clique D hij
      rw [hi,hj] at hadj
      obtain ⟨hne,e,he⟩ := hadj
      have heface : e ∈ N.star v := by
        have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
        rcases hfin i j hij with h | h
        · have ep : s(D.tail e,D.head e) = s(D.tail ((face v).edge i),D.head ((face v).edge i)) := by
            rw [(face v).edge_ends, ← h, hi, hj]
            exact Sym2.eq_iff.mpr he
          have ee := sD.pair_injective ep
          rw [ee]
          have hm : (face v).edge i ∈ Finset.univ.image (face v).edge :=
            Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
          rwa [(face v).edge_range] at hm
        · have ep : s(D.tail e,D.head e) = s(D.tail ((face v).edge j),D.head ((face v).edge j)) := by
            rw [(face v).edge_ends, ← h, hi, hj]
            exact Sym2.eq_iff.mpr he.symm
          rw [sD.pair_injective ep]
          have hm : (face v).edge j ∈ Finset.univ.image (face v).edge :=
            Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
          rwa [(face v).edge_range] at hm
      have heA : e ∈ N.regionEdges A := by
        rcases (N.mem_star e v).mp heface with h | h
        · exact (N.mem_regionEdges A e).mpr (Or.inl (h ▸ hv))
        · exact (N.mem_regionEdges A e).mpr (Or.inr (h ▸ hv))
      apply SimpleGraph.Adj.reachable
      refine ⟨fun h => hne (congrArg Subtype.val h),⟨e,heA⟩,?_⟩
      exact he.elim (fun h => Or.inl ⟨Subtype.ext h.1,Subtype.ext h.2⟩)
        (fun h => Or.inr ⟨Subtype.ext h.1,Subtype.ext h.2⟩)
  have step {v w : {v // v ∈ A}} (hvw : (N.graph.induce {v | v ∈ A}).Adj v w) :
      R.graph.Reachable (a v) (a w) := by
    obtain ⟨_,e,he⟩ := hvw
    have hv : N.Incident e v.val := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
    have hw : N.Incident e w.val := he.elim (fun h => Or.inr h.2) (fun h => Or.inl h.1)
    have hf (u : V) (hu : N.Incident e u) : D.tail e ∈ Set.range (face u).corner :=
      ((face u).corner_iff_incident D _).mpr ⟨e,(N.mem_star e u).mpr hu,Or.inl rfl⟩
    let z : N.regionVertices D A := ⟨D.tail e,in_face v.property (hf _ hv)⟩
    exact (local_path v.property ⟨0,rfl⟩ (hf _ hv)).trans
      (local_path w.property (z := z) (hf _ hw) ⟨0,rfl⟩)
  have all_faces {v w : {v // v ∈ A}} : R.graph.Reachable (a v) (a w) := by
    obtain ⟨p⟩ := hA v w
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons h p ih => exact (step h).trans ih
  obtain ⟨v₀⟩ := hA.nonempty
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨a v₀,?_⟩
  intro z
  obtain ⟨e,he,hz⟩ := (N.mem_regionVertices D A z.val).mp z.property
  rcases (N.mem_regionEdges A e).mp he with ht | hh
  · have hf := ((face (N.tail e)).corner_iff_incident D z.val).mpr
      ⟨e,(N.mem_star _ _).mpr (Or.inl rfl),hz⟩
    exact (all_faces (w := ⟨N.tail e,ht⟩)).trans (local_path ht ⟨0,rfl⟩ hf)
  · have hf := ((face (N.head e)).corner_iff_incident D z.val).mpr
      ⟨e,(N.mem_star _ _).mpr (Or.inr rfl),hz⟩
    exact (all_faces (w := ⟨N.head e,hh⟩)).trans (local_path hh ⟨0,rfl⟩ hf)

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

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.region_connected := @_root_.OAI.Barnette.Network.region_connected
