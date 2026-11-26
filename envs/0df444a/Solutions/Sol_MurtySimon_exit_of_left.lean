-- Prove2me | solution 1 for MurtySimon.exit_of_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:04:19.527092+00:00
-- url     : https://prove2.me/submissions/719fe111-4318-4b5d-9780-07cada6ebabf

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_mate_spec
public import Theorems.Thm_MurtySimon_IsEdgeMatching_adj_mate
public import Theorems.Thm_MurtySimon_isMid_of_isCrit
public import Theorems.Thm_MurtySimon_OnPath_mem_edgeSet
public import Theorems.Thm_MurtySimon_aux_adj
public import Theorems.Thm_MurtySimon_comp_count
public import Theorems.Thm_MurtySimon_mem_Lt
public import Theorems.Thm_MurtySimon_mem_Rt
public import Theorems.Thm_MurtySimon_mem_neighborFinset_right
public import Theorems.Thm_MurtySimon_onPath_iff


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable {M : Finset (Sym2 V)}
variable (hM : IsEdgeMatching G M) {C : (aux G M).ConnectedComponent}
  (hC : cA G M C = cB G M C + 1)
include hM hC
namespace MurtySimon
theorem _root_.solution {a b : V} (ha : Covered M a) (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hL : s(mate M a, b) ∈ Lt G M) (hLC : (aux G M).connectedComponentMk s(mate M a, b) = C) :
    (a, b) ∈ exits G M ∧ compOf G M (a, b) = C := by
  refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_, ha, mem_union_left _ hL⟩, hLC⟩
  · rw [mem_edgeSet, compl_adj]; exact ⟨hab, hnadj⟩
  · intro hcrit
    have hmid : IsMid G a b (mate M a) := isMid_of_isCrit hcrit (hM.adj_mate ha) (mem_Lt.1 hL).1
    -- the critical non-edge `ab` has only one neighbour in `𝓘'`
    have hdeg := (comp_count M C).2 hC |>.1 s(a, b) (mem_Rt.2 hcrit) (by
      rw [← hLC]
      apply ConnectedComponent.connectedComponentMk_eq_of_adj
      rw [aux_adj]
      exact Or.inr ⟨(mem_Lt.1 hL).2, (onPath_iff hmid).2 (Or.inr rfl)⟩)
    have hsub : (aux G M).neighborFinset s(a, b) ⊆ {s(mate M a, b)} := by
      intro e he
      obtain ⟨h1 | h1, h2⟩ := (mem_neighborFinset_right hmid).1 he
      · exact absurd (h1 ▸ mate_spec ha) h2
      · exact mem_singleton.2 h1
    have := card_le_card hsub
    rw [card_singleton] at this
    omega
end MurtySimon
