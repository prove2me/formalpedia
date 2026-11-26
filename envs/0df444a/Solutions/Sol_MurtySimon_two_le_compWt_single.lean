-- Prove2me | solution 1 for MurtySimon.two_le_compWt_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:43.961045+00:00
-- url     : https://prove2.me/submissions/1321e6ba-d020-4ce5-9fd0-e979bebd7cdc

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_mate_spec
public import Theorems.Thm_MurtySimon_IsEdgeMatching_mate_mate
public import Theorems.Thm_MurtySimon_covered_mate
public import Theorems.Thm_MurtySimon_IsEdgeMatching_adj_mate
public import Theorems.Thm_MurtySimon_IsMaximalEdgeMatching_covered
public import Theorems.Thm_MurtySimon_two_le_compWt_of_safe
public import Theorems.Thm_MurtySimon_two_le_compWt_of_two
public import Theorems.Thm_MurtySimon_exit_of_left
public import Theorems.Thm_MurtySimon_IsMid_symm
public import Theorems.Thm_MurtySimon_OnPath_mem_edgeSet
public import Theorems.Thm_MurtySimon_OnPath_ne
public import Theorems.Thm_MurtySimon_aux_adj
public import Theorems.Thm_MurtySimon_aux_adj_cases
public import Theorems.Thm_MurtySimon_exists_onPath_of_triangle
public import Theorems.Thm_MurtySimon_mem_Lt
public import Theorems.Thm_MurtySimon_not_mem_Rt_of_mem_Lt


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
theorem _root_.solution (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G)
    (h1 : cA G M C = 1) : 2 ≤ compWt C := by
  have hB : cB G M C = 0 := by omega
  obtain ⟨e, he⟩ := card_eq_one.1 h1
  have hmem : e ∈ (Lt G M).filter fun e => (aux G M).connectedComponentMk e = C := by
    rw [he]; exact mem_singleton_self e
  have heL : e ∈ Lt G M := (mem_filter.1 hmem).1
  have heC : (aux G M).connectedComponentMk e = C := (mem_filter.1 hmem).2
  -- `e` has no neighbours in `𝓘'`
  have hnb : ∀ f, ¬ (aux G M).Adj e f := by
    intro f hf
    have hfR : f ∈ Rt G := by
      rcases aux_adj_cases hf with h | h
      · exact h.2.1
      · exact absurd h.2.1 (not_mem_Rt_of_mem_Lt heL)
    have hfC : (aux G M).connectedComponentMk f = C :=
      (ConnectedComponent.connectedComponentMk_eq_of_adj hf).symm.trans heC
    have : f ∈ (Rt G).filter fun f => (aux G M).connectedComponentMk f = C :=
      mem_filter.2 ⟨hfR, hfC⟩
    have h0 : cB G M C = #((Rt G).filter fun f => (aux G M).connectedComponentMk f = C) := rfl
    rw [hB] at h0
    exact absurd (h0 ▸ card_pos.2 ⟨f, this⟩ : 0 < 0) (lt_irrefl 0)
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨hxy, hxyM⟩ := mem_Lt.1 heL
    rw [mem_edgeSet] at hxy
    -- from a covered endpoint we get a switch exit
    have key : ∀ a b, s(a, b) = s(x, y) → Covered M a →
        (mate M a, b) ∈ exits G M ∧ compOf G M (mate M a, b) = C := by
      intro a b hab ha
      have hadj : G.Adj a b := by rw [← mem_edgeSet, hab]; exact hxy
      have habM : s(a, b) ∉ M := hab ▸ hxyM
      have hne : mate M a ≠ b := fun h => habM (h ▸ mate_spec ha)
      have hnadj : ¬ G.Adj (mate M a) b := by
        intro h'
        obtain ⟨f, hf⟩ := exists_onPath_of_triangle hG hadj (hM.adj_mate ha) h'
        exact hnb f (hab ▸ aux_adj.2 (Or.inl ⟨habM, hf⟩))
      have hmm : mate M (mate M a) = a := hM.mate_mate ha
      exact exit_of_left hM hC (covered_mate ha) hne hnadj (by rw [hmm, hab]; exact heL)
        (by rw [hmm, hab]; exact heC)
    rcases hmax.covered hxy hxyM with hx | hy
    · obtain ⟨hp, hpC⟩ := key x y rfl hx
      by_cases hy : Covered M y
      · obtain ⟨hq, hqC⟩ := key y x Sym2.eq_swap hy
        refine two_le_compWt_of_two hp hpC hq hqC ?_
        intro h
        exact hxy.ne (Prod.ext_iff.1 h).2.symm
      · exact two_le_compWt_of_safe hp hpC hy
    · obtain ⟨hp, hpC⟩ := key y x Sym2.eq_swap hy
      by_cases hx : Covered M x
      · obtain ⟨hq, hqC⟩ := key x y rfl hx
        refine two_le_compWt_of_two hp hpC hq hqC ?_
        intro h
        exact hxy.ne (Prod.ext_iff.1 h).2
      · exact two_le_compWt_of_safe hp hpC hx
end MurtySimon
