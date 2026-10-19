-- Prove2me | solution 1 for OAI.Barnette.Network.complement_singleton_root
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:18:43.258935+00:00
-- url     : https://prove2.me/submissions/2eb17473-c7e1-4128-b38a-8511fd407852

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Contraction.lean:L406-L424
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.complement_singleton_root. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_Network_card_star
import Theorems.Thm_OAI_Barnette_Network_rim_cut_count
import Theorems.Thm_OAI_Barnette_Network_rim_three_cut

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

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
lemma rim_three_no_internal (hN : N.ThreeEdgeConnected) (U : Finset F)
    (_hm : 3 ≤ (D.inducedEdges U).card) (q : N.Regions D U) (hq : N.rim D U q = 3)
    {e : E} (he : e ∈ D.inducedEdges U) :
    ¬(N.tail e ∈ N.regionShore D U q ∧ N.head e ∈ N.regionShore D U q) := by
  have hc := N.rim_three_cut D hN U _hm q hq
  have hh := N.rim_cut_count D U q
  have hz : ((D.inducedEdges U).filter fun e =>
      N.tail e ∈ N.regionShore D U q ∧ N.head e ∈ N.regionShore D U q) = ∅ :=
    Finset.card_eq_zero.mp (by omega)
  intro hi
  have hhmem : e ∈ (D.inducedEdges U).filter (fun e =>
      N.tail e ∈ N.regionShore D U q ∧ N.head e ∈ N.regionShore D U q) :=
    Finset.mem_filter.mpr ⟨he,hi⟩
  rw [hz] at hhmem
  exact Finset.notMem_empty _ hhmem

lemma star_subset_eq (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    {v w : V} (hvw : N.star v ⊆ N.star w) : v = w := by
  by_contra hne
  have hc : 1 < (N.star v).card := by rw [N.card_star hN,h3 v]; decide
  obtain ⟨e,he,f,hf,hef⟩ := Finset.one_lt_card.mp hc
  have ends {e : E} (he : e ∈ N.star v) : s(N.tail e,N.head e) = s(v,w) := by
    have hv := (N.mem_star e v).mp he
    have hw := (N.mem_star e w).mp (hvw he)
    apply Sym2.eq_iff.mpr
    rcases hv with hv | hv <;> rcases hw with hw | hw
    · exact (hne (hv.symm.trans hw)).elim
    · exact Or.inl ⟨hv,hw⟩
    · exact Or.inr ⟨hw,hv⟩
    · exact (hne (hv.symm.trans hw)).elim
  exact hef (hN.pair_injective ((ends he).trans (ends hf).symm))

omit [Fintype F] in
lemma complement_singleton_root (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (hcut : N.ThreeEdgeConnected) (U : Finset F) (root : V)
    (hr : N.star root ⊆ D.inducedEdges U) (q : N.Regions D U)
    (hq : N.rim D U q = 3) {v : V} (hv : (N.regionShore D U q)ᶜ = {v}) : v = root := by
  have hm : 3 ≤ (D.inducedEdges U).card := by
    have hh := Finset.card_le_card hr
    rwa [N.card_star hN,h3 root] at hh
  apply (N.star_subset_eq hN h3 (v := root) (w := v) ?_).symm
  intro e he
  have hn := N.rim_three_no_internal D hcut U hm q hq (hr he)
  rw [N.mem_star]
  have ht : N.tail e ∉ N.regionShore D U q ↔ N.tail e = v := by
    rw [← Finset.mem_compl,hv,Finset.mem_singleton]
  have hh : N.head e ∉ N.regionShore D U q ↔ N.head e = v := by
    rw [← Finset.mem_compl,hv,Finset.mem_singleton]
  rcases not_and_or.mp hn with ht' | hh'
  · exact Or.inl (ht.mp ht')
  · exact Or.inr (hh.mp hh')

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.complement_singleton_root := @_root_.OAI.Barnette.Network.complement_singleton_root
