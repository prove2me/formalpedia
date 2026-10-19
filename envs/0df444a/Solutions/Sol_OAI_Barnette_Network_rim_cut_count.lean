-- Prove2me | solution 1 for OAI.Barnette.Network.rim_cut_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:14:48.180113+00:00
-- url     : https://prove2.me/submissions/4f58fc7a-1f6a-45af-8ac3-9d64a3c653e1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Contraction.lean:L304-L319
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.rim_cut_count. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction

-- ---- from OAI.Combinatorics.Hamiltonian.Network ----
namespace OAI

/-! Oriented finite networks, cycle and cut spaces, and graph realization. -/

namespace Barnette

namespace Network
noncomputable section
variable {V E : Type*} (N : Network V E)

theorem edge_reachable (e : E) : N.graph.Reachable (N.tail e) (N.head e) := by
  by_cases h : N.tail e = N.head e
  · rw [h]
  · exact (show N.graph.Adj (N.tail e) (N.head e) from
      ⟨h, e, Or.inl ⟨rfl, rfl⟩⟩).reachable

variable [Fintype V] [Fintype E]
attribute [local instance] OAI.Barnette.Network.instDecidableEq
attribute [local instance] OAI.Barnette.Network.instDecidableEq_1
variable {F : Type*} [Fintype F] (D : Network F E)

end
end Network
end Barnette

namespace Barnette
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj]

end
end Barnette

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.Contraction ----
namespace OAI

/-! Contraction and deletion of finite oriented dual networks. -/

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

omit [Fintype F] in
lemma regionShore_off_edge (U : Finset F) (q : N.Regions D U) {e : E}
    (he : e ∉ D.inducedEdges U) :
    N.tail e ∈ N.regionShore D U q ↔ N.head e ∈ N.regionShore D U q := by
  simp only [N.mem_regionShore]
  have hh : (N.regions D U).componentMap (N.tail e) =
      (N.regions D U).componentMap (N.head e) :=
    SimpleGraph.ConnectedComponent.sound ((N.regions D U).edge_reachable ⟨e,he⟩)
  rw [hh]

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
lemma region_cut_subset (U : Finset F) (q : N.Regions D U) :
    N.cut (N.regionShore D U q) ⊆ D.inducedEdges U := by
  intro e he
  by_contra hn
  have hh := N.regionShore_off_edge D U q hn
  have hc := (N.mem_cut _ _).mp he
  exact hc.elim (fun h => h.2 (hh.mp h.1)) (fun h => h.2 (hh.mpr h.1))

omit [Fintype F] in
lemma rim_cut_count (U : Finset F) (q : N.Regions D U) :
    N.rim D U q = (N.cut (N.regionShore D U q)).card +
      2 * ((D.inducedEdges U).filter fun e =>
        N.tail e ∈ N.regionShore D U q ∧ N.head e ∈ N.regionShore D U q).card := by
  have hcut : N.cut (N.regionShore D U q) =
      (D.inducedEdges U).filter fun e => e ∈ N.cut (N.regionShore D U q) := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun he => ⟨N.region_cut_subset D U q he,he⟩,And.right⟩
  rw [hcut]
  simp only [rim,Finset.card_filter,Finset.mul_sum,← Finset.sum_add_distrib,N.mem_cut]
  apply Finset.sum_congr rfl
  intro e _
  by_cases ht : N.tail e ∈ N.regionShore D U q <;>
    by_cases hh : N.head e ∈ N.regionShore D U q <;> simp [ht,hh]

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.rim_cut_count := @_root_.OAI.Barnette.Network.rim_cut_count
