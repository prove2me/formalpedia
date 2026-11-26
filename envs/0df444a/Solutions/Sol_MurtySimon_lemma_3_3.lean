-- Prove2me | solution 1 for MurtySimon.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:18:49.217429+00:00
-- url     : https://prove2.me/submissions/3e87347c-7972-4950-97f4-609c40e3499a

module
public import Definitions.Def_MurtySimon_Bound
public import Definitions.Def_MurtySimon_Equality
public import Theorems.Thm_MurtySimon_exists_maximal_extension
public import Theorems.Thm_MurtySimon_isEdgeMatching_pair
public import Theorems.Thm_MurtySimon_emb_mk
public import Theorems.Thm_MurtySimon_sum_pieces
public import Theorems.Thm_MurtySimon_card_LC0_split
public import Theorems.Thm_MurtySimon_lemma_3_2
public import Theorems.Thm_MurtySimon_IsEdgeMatching_mate_eq
public import Theorems.Thm_MurtySimon_IsMid_isCrit
public import Theorems.Thm_MurtySimon_IsMid_ne_left
public import Theorems.Thm_MurtySimon_IsMid_ne_right
public import Theorems.Thm_MurtySimon_IsMid_symm
public import Theorems.Thm_MurtySimon_OnPath_isCrit
public import Theorems.Thm_MurtySimon_OnPath_mem_edgeSet
public import Theorems.Thm_MurtySimon_aux_adj
public import Theorems.Thm_MurtySimon_aux_adj_cases
public import Theorems.Thm_MurtySimon_comp_count
public import Theorems.Thm_MurtySimon_eq_case_conditions
public import Theorems.Thm_MurtySimon_isMid_of_isCrit
public import Theorems.Thm_MurtySimon_mem_Lt
public import Theorems.Thm_MurtySimon_mem_Rt
public import Theorems.Thm_MurtySimon_not_mem_Rt_of_mem_Lt
public import Theorems.Thm_MurtySimon_onPath_iff


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution (hG : IsCritical G) (heq : EqCase G) (C : (aux G ∅).ConnectedComponent)
    (hC : cA G ∅ C = cB G ∅ C + 1) (hB : 1 ≤ cB G ∅ C) :
    ∃ u, ∀ a b, G.Adj a b → a = u ∨ b = u := by
  obtain ⟨ℓ, hℓL, -, -, -, hℓC, -, hℓd, -⟩ := (comp_count ∅ C).2 hC |>.2 (by omega)
  have hone := (lemma_3_2 hG heq C (by omega)).2
  obtain ⟨f, hf⟩ := card_eq_one.1 hℓd
  have hℓf : (aux G ∅).Adj ℓ f := (mem_neighborFinset _ _ _).1 (hf ▸ mem_singleton_self f)
  have hnbr : ∀ g, (aux G ∅).Adj ℓ g → g = f := fun g hg =>
    mem_singleton.1 (hf ▸ (mem_neighborFinset _ _ _).2 hg)
  have hfC : (aux G ∅).connectedComponentMk f = C :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj hℓf).symm.trans hℓC
  have hon : OnPath G ℓ f := by
    rcases aux_adj_cases hℓf with h | h
    · exact h.2.2
    · exact absurd h.2.1 (not_mem_Rt_of_mem_Lt hℓL)
  obtain ⟨x, y, u, rfl, hm, hℓ⟩ : ∃ x y u, f = s(x, y) ∧ IsMid G x y u ∧ ℓ = s(u, y) := by
    obtain ⟨x, y, u, rfl, hm, rfl⟩ := hon
    exact ⟨y, x, u, Sym2.eq_swap, hm.symm, Sym2.eq_swap⟩
  subst hℓ
  have hxu : G.Adj x u := hm.2.2.1
  have huy : G.Adj u y := hm.2.2.2.1
  have hxy : x ≠ y := hm.1
  have hux : u ≠ x := hm.ne_left
  have huy' : u ≠ y := hm.ne_right
  have hxuC : (aux G ∅).connectedComponentMk s(x, u) = C := by
    rw [← hfC]
    apply ConnectedComponent.connectedComponentMk_eq_of_adj
    rw [aux_adj]
    exact Or.inl ⟨notMem_empty _, (onPath_iff hm).2 (Or.inl rfl)⟩
  have hℓLC : s(u, y) ∈ LC0 C := mem_filter.2 ⟨hℓL, hℓC⟩
  by_cases h3 : ∀ v, G.Adj x v → v = u
  · -- Case 3: `u` is adjacent to every other vertex, and every edge contains `u`
    have hall : ∀ w, w ≠ u → G.Adj u w := by
      intro w hwu
      by_cases hwx : w = x
      · rw [hwx]; exact hxu.symm
      rcases hG.1 x w (Ne.symm hwx) with h | ⟨z, hz1, hz2⟩
      · exact absurd (h3 w h) hwu
      · rw [h3 z hz1] at hz2; exact hz2
    refine ⟨u, fun a b hab => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hau, hbu⟩ := hcon
    have hnot : ∀ w, s(u, w) ≠ s(a, b) := by
      intro w h
      have : u ∈ s(a, b) := h ▸ Sym2.mem_mk_left u w
      rcases Sym2.mem_iff.1 this with h' | h'
      · exact hau h'.symm
      · exact hbu h'.symm
    apply hG.2 s(a, b) hab
    intro p q hpq
    simp only [deleteEdges_adj, Set.mem_singleton_iff]
    by_cases hp : p = u
    · subst hp
      exact Or.inl ⟨hall q (Ne.symm hpq), hnot q⟩
    by_cases hq : q = u
    · subst hq
      exact Or.inl ⟨(hall p hp).symm, by rw [Sym2.eq_swap]; exact hnot p⟩
    exact Or.inr ⟨u, ⟨(hall p hp).symm, by rw [Sym2.eq_swap]; exact hnot p⟩,
      ⟨hall q hq, hnot q⟩⟩
  push Not at h3
  obtain ⟨v, hxv, hvu⟩ := h3
  exfalso
  have hvx : v ≠ x := hxv.ne'
  have hvy : v ≠ y := fun h => hm.2.1 (h ▸ hxv)
  -- the matching `{uy, xv}` and a maximal extension
  have hN : IsEdgeMatching G {s(u, y), s(x, v)} :=
    isEdgeMatching_pair huy hxv hux (Ne.symm hvu) (Ne.symm hxy) hvy.symm
  obtain ⟨M, hNM, hmax⟩ := exists_maximal_extension hN
  have hM := hmax.1
  have huyM : s(u, y) ∈ M := hNM (mem_insert_self _ _)
  have hxvM : s(x, v) ∈ M := hNM (mem_insert_of_mem (mem_singleton_self _))
  have hmatev : mate M v = x := hM.mate_eq (Sym2.eq_swap ▸ hxvM)
  have hcovv : Covered M v := ⟨x, Sym2.eq_swap ▸ hxvM⟩
  -- exactly one left vertex of `C` lies in `M`, so every piece of `C` is balanced
  have hc : #((LC0 C).filter (· ∈ M)) = 1 := by
    have h1 := hone M hM
    have h2 : 1 ≤ #((LC0 C).filter (· ∈ M)) := card_pos.2 ⟨_, mem_filter.2 ⟨hℓLC, huyM⟩⟩
    omega
  have hbal : ∀ D, emb G M D = C → cA G M D = cB G M D := by
    have hsum := sum_pieces M C
    have hsplit := card_LC0_split M C
    have hzero : ∑ D ∈ (univ : Finset (aux G M).ConnectedComponent).filter
        (fun D => emb G M D = C), ((cA G M D : ℤ) - cB G M D) = 0 := by
      rw [hsum]; omega
    have hnn : ∀ D ∈ (univ : Finset (aux G M).ConnectedComponent).filter
        (fun D => emb G M D = C), 0 ≤ ((cA G M D : ℤ) - cB G M D) := by
      intro D _
      have := (eq_case_conditions hmax hG (heq M hmax)).1 D
      omega
    intro D hD
    have := (sum_eq_zero_iff_of_nonneg hnn).1 hzero D (mem_filter.2 ⟨mem_univ _, hD⟩)
    omega
  have hnoexit : ∀ p ∈ exits G M, emb G M (compOf G M p) ≠ C := by
    intro p hp hpC
    exact (eq_case_conditions hmax hG (heq M hmax)).2 _ (hbal _ hpC) p hp rfl
  by_cases huv : G.Adj u v
  · -- Case 2: `v` is a common neighbour of `x` and `u`
    have hnyv : ¬ G.Adj y v := fun h => hvu (hm.2.2.2.2 v hxv h.symm)
    have hnc : ¬ IsCrit G s(y, v) := by
      intro hcrit
      have hm' : IsMid G y v u := isMid_of_isCrit hcrit huy.symm huv
      have hadj : (aux G ∅).Adj s(u, y) s(y, v) := by
        rw [aux_adj]
        exact Or.inl ⟨notMem_empty _, (onPath_iff hm').2 (Or.inl Sym2.eq_swap)⟩
      have := hnbr _ hadj
      rw [Sym2.eq_swap (a := x)] at this
      exact hvx (Sym2.congr_right.1 this)
    apply hnoexit (v, y)
    · refine mem_filter.2 ⟨mem_univ _, ?_, ?_, hcovv, ?_⟩
      · rw [mem_edgeSet, compl_adj]; exact ⟨hvy, fun h => hnyv h.symm⟩
      · rw [Sym2.eq_swap]; exact hnc
      · rw [hmatev]; exact mem_union_right _ (mem_Rt.2 hm.isCrit)
    · simp only [compOf, hmatev, emb_mk]; exact hfC
  · -- Case 1: `v` is a neighbour of `x` not adjacent to `u`
    have hnc : ¬ IsCrit G s(u, v) := by
      intro hcrit
      have hm' : IsMid G u v x := isMid_of_isCrit hcrit hxu.symm hxv
      have h1 : (aux G ∅).Adj s(x, v) s(u, v) := by
        rw [aux_adj]
        exact Or.inl ⟨notMem_empty _, (onPath_iff hm').2 (Or.inr rfl)⟩
      have h2 : (aux G ∅).Adj s(x, u) s(u, v) := by
        rw [aux_adj]
        exact Or.inl ⟨notMem_empty _, (onPath_iff hm').2 (Or.inl Sym2.eq_swap)⟩
      have hxvC : (aux G ∅).connectedComponentMk s(x, v) = C := by
        rw [ConnectedComponent.connectedComponentMk_eq_of_adj h1,
          ← ConnectedComponent.connectedComponentMk_eq_of_adj h2]
        exact hxuC
      have hxvL : s(x, v) ∈ LC0 C := mem_filter.2 ⟨mem_Lt.2 ⟨hxv, notMem_empty _⟩, hxvC⟩
      have hsub : ({s(u, y), s(x, v)} : Finset (Sym2 V)) ⊆
          (LC0 C).filter (· ∈ ({s(u, y), s(x, v)} : Finset (Sym2 V))) := by
        intro e he
        rcases mem_insert.1 he with rfl | he
        · exact mem_filter.2 ⟨hℓLC, mem_insert_self _ _⟩
        · rw [mem_singleton.1 he]
          exact mem_filter.2 ⟨hxvL, mem_insert_of_mem (mem_singleton_self _)⟩
      have hne : s(u, y) ≠ s(x, v) := by
        intro h
        rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hux h1
        · exact hvu h1.symm
      have := card_le_card hsub
      rw [card_pair hne] at this
      have := hone _ hN
      omega
    have hxuM : s(x, u) ∉ M := by
      intro h
      have := hM.mate_eq h
      rw [hM.mate_eq hxvM] at this
      exact hvu this
    apply hnoexit (v, u)
    · refine mem_filter.2 ⟨mem_univ _, ?_, ?_, hcovv, ?_⟩
      · rw [mem_edgeSet, compl_adj]; exact ⟨hvu, fun h => huv h.symm⟩
      · rw [Sym2.eq_swap]; exact hnc
      · rw [hmatev]; exact mem_union_left _ (mem_Lt.2 ⟨hxu, hxuM⟩)
    · simp only [compOf, hmatev, emb_mk]; exact hxuC
end MurtySimon
