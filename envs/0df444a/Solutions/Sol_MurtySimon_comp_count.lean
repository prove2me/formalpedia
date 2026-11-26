-- Prove2me | solution 1 for MurtySimon.comp_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:57:42.14904+00:00
-- url     : https://prove2.me/submissions/c2359ee2-b110-4a68-aa52-aaeaceb38fce

module
public import Definitions.Def_MurtySimon_Basic
public import Definitions.Def_MurtySimon_Components
public import Theorems.Thm_MurtySimon_not_mem_Rt_of_mem_Lt
public import Theorems.Thm_MurtySimon_aux_adj_cases
public import Theorems.Thm_MurtySimon_card_neighborFinset_right_le
public import Theorems.Thm_MurtySimon_exists_adj_of_reachable
public import Theorems.Thm_MurtySimon_IsMid_symm
public import Theorems.Thm_MurtySimon_OnPath_mem_edgeSet


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution (M : Finset (Sym2 V)) (C : (aux G M).ConnectedComponent) :
    cA G M C ≤ cB G M C + 1 ∧
    (cA G M C = cB G M C + 1 →
      (∀ f ∈ Rt G, (aux G M).connectedComponentMk f = C →
        #((aux G M).neighborFinset f) = 2) ∧
      (2 ≤ cA G M C → ∃ l₁ ∈ Lt G M, ∃ l₂ ∈ Lt G M, l₁ ≠ l₂ ∧
        (aux G M).connectedComponentMk l₁ = C ∧ (aux G M).connectedComponentMk l₂ = C ∧
        #((aux G M).neighborFinset l₁) = 1 ∧ #((aux G M).neighborFinset l₂) = 1)) := by
  set LC := (Lt G M).filter fun e => (aux G M).connectedComponentMk e = C with hLC
  set RC := (Rt G).filter fun f => (aux G M).connectedComponentMk f = C with hRC
  have hA : cA G M C = #LC := rfl
  have hB : cB G M C = #RC := rfl
  rw [hA, hB]
  have hR2 : ∀ f ∈ RC, #((aux G M).neighborFinset f) ≤ 2 := fun f hf =>
    card_neighborFinset_right_le (mem_filter.1 hf).1
  have hRsub : ∀ f ∈ RC, (aux G M).neighborFinset f ⊆ LC := by
    intro f hf z hz
    rw [mem_neighborFinset] at hz
    obtain ⟨hf1, hf2⟩ := mem_filter.1 hf
    refine mem_filter.2 ⟨?_, ?_⟩
    · rcases aux_adj_cases hz with h | h
      · exact absurd h.1 (fun h' => not_mem_Rt_of_mem_Lt h' hf1)
      · exact h.1
    · rw [← hf2]; exact (ConnectedComponent.connectedComponentMk_eq_of_adj hz).symm
  have hLsub : ∀ e ∈ LC, (aux G M).neighborFinset e ⊆ RC := by
    intro e he z hz
    rw [mem_neighborFinset] at hz
    obtain ⟨he1, he2⟩ := mem_filter.1 he
    refine mem_filter.2 ⟨?_, ?_⟩
    · rcases aux_adj_cases hz with h | h
      · exact h.2.1
      · exact absurd h.2.1 (not_mem_Rt_of_mem_Lt he1)
    · rw [← he2]; exact (ConnectedComponent.connectedComponentMk_eq_of_adj hz).symm
  have hsum : ∑ e ∈ LC, #((aux G M).neighborFinset e) = ∑ f ∈ RC, #((aux G M).neighborFinset f) := by
    have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := LC) (t := RC) (r := (aux G M).Adj)
    have e1 : ∀ e ∈ LC, #(bipartiteAbove (aux G M).Adj RC e) = #((aux G M).neighborFinset e) := by
      intro e he
      congr 1
      ext z
      simp only [bipartiteAbove, mem_filter, mem_neighborFinset]
      exact ⟨fun h => h.2, fun h => ⟨hLsub e he (by simpa using h), h⟩⟩
    have e2 : ∀ f ∈ RC, #(bipartiteBelow (aux G M).Adj LC f) = #((aux G M).neighborFinset f) := by
      intro f hf
      congr 1
      ext z
      simp only [bipartiteBelow, mem_filter, mem_neighborFinset]
      exact ⟨fun h => h.2.symm, fun h => ⟨hRsub f hf (by simpa using h), h.symm⟩⟩
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2] at h
    exact h
  -- the key inequality `a + b ≤ e(C) + 1 ≤ ∑_{f ∈ RC} deg f + 1`
  have hkey : #LC + #RC ≤ ∑ f ∈ RC, #((aux G M).neighborFinset f) + 1 := by
    by_cases hS : (LC ∪ RC).Nonempty
    swap
    · rw [not_nonempty_iff_eq_empty, union_eq_empty] at hS
      rw [hS.1, hS.2]; simp
    obtain ⟨w, hw⟩ := hS
    have hwC : (aux G M).connectedComponentMk w = C := by
      rcases mem_union.1 hw with h | h <;> exact (mem_filter.1 h).2
    have hwLR : w ∈ Lt G M ∨ w ∈ Rt G := by
      rcases mem_union.1 hw with h | h
      · exact Or.inl (mem_filter.1 h).1
      · exact Or.inr (mem_filter.1 h).1
    have hall : ∀ v, (aux G M).connectedComponentMk v = C → v ∈ LC ∪ RC := by
      intro v hv
      have hvLR : v ∈ Lt G M ∨ v ∈ Rt G := by
        by_cases hvw : v = w
        · rw [hvw]; exact hwLR
        obtain ⟨z, hz⟩ := exists_adj_of_reachable
          (ConnectedComponent.exact (hv.trans hwC.symm)) hvw
        rcases aux_adj_cases hz with h | h
        · exact Or.inl h.1
        · exact Or.inr h.2.1
      rcases hvLR with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨h, hv⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨h, hv⟩)
    have hdisj : Disjoint LC RC := by
      rw [Finset.disjoint_left]
      intro e he he'
      exact not_mem_Rt_of_mem_Lt (mem_filter.1 he).1 (mem_filter.1 he').1
    have hcard : Nat.card C = #LC + #RC := by
      rw [← card_union_of_disjoint hdisj, Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext v
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro hv; exact hall v hv
      · intro hv
        rcases mem_union.1 hv with h | h <;> exact (mem_filter.1 h).2
    have hconn := C.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
    set T := RC.biUnion fun f => ((aux G M).neighborFinset f).image fun e => s(f, e) with hT
    have hTle : #T ≤ ∑ f ∈ RC, #((aux G M).neighborFinset f) :=
      card_biUnion_le.trans (sum_le_sum fun f _ => card_image_le)
    have hmem : ∀ e ∈ C.toSimpleGraph.edgeSet, Sym2.map Subtype.val e ∈ T := by
      intro e he
      induction e using Sym2.ind with
      | h a b =>
        rw [mem_edgeSet] at he
        have hab : (aux G M).Adj a.1 b.1 := he
        have ha : (aux G M).connectedComponentMk a.1 = C := a.2
        have hb : (aux G M).connectedComponentMk b.1 = C := b.2
        simp only [Sym2.map_mk, hT, mem_biUnion, mem_image, mem_neighborFinset]
        rcases aux_adj_cases hab with h | h
        · exact ⟨b.1, mem_filter.2 ⟨h.2.1, hb⟩, a.1, hab.symm, Sym2.eq_swap⟩
        · exact ⟨a.1, mem_filter.2 ⟨h.2.1, ha⟩, b.1, hab, rfl⟩
    have hedge : Nat.card C.toSimpleGraph.edgeSet ≤ #T := by
      have hinj : Function.Injective fun e : C.toSimpleGraph.edgeSet =>
          (⟨Sym2.map Subtype.val e.1, hmem e.1 e.2⟩ : (T : Set (Sym2 (Sym2 V)))) := by
        intro e₁ e₂ h
        apply Subtype.ext
        exact Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h)
      calc Nat.card C.toSimpleGraph.edgeSet ≤ Nat.card (T : Set (Sym2 (Sym2 V))) :=
            Nat.card_le_card_of_injective _ hinj
        _ = #T := by simp
    omega
  have hsumle : ∑ f ∈ RC, #((aux G M).neighborFinset f) ≤ 2 * #RC := by
    calc ∑ f ∈ RC, #((aux G M).neighborFinset f) ≤ ∑ _f ∈ RC, 2 := sum_le_sum hR2
      _ = 2 * #RC := by rw [sum_const, smul_eq_mul, mul_comm]
  refine ⟨by omega, fun heq => ⟨?_, ?_⟩⟩
  · -- every right vertex of `C` has degree exactly two
    intro f hf hfC
    have hfRC : f ∈ RC := mem_filter.2 ⟨hf, hfC⟩
    by_contra hne
    have hlt : #((aux G M).neighborFinset f) < 2 := lt_of_le_of_ne (hR2 f hfRC) hne
    have : ∑ g ∈ RC, #((aux G M).neighborFinset g) < ∑ _g ∈ RC, 2 :=
      sum_lt_sum hR2 ⟨f, hfRC, hlt⟩
    rw [sum_const, smul_eq_mul] at this
    omega
  · -- two leaves
    intro h2
    have hsumL : ∑ e ∈ LC, #((aux G M).neighborFinset e) + 2 = 2 * #LC := by omega
    -- every left vertex has a neighbour
    have hpos : ∀ e ∈ LC, 1 ≤ #((aux G M).neighborFinset e) := by
      intro e he
      obtain ⟨e', he', hne⟩ : ∃ e' ∈ LC, e' ≠ e := by
        by_contra hcon
        push Not at hcon
        have : LC ⊆ {e} := fun z hz => mem_singleton.2 (hcon z hz)
        have := card_le_card this
        simp at this
        omega
      obtain ⟨z, hz⟩ := exists_adj_of_reachable
        (ConnectedComponent.exact ((mem_filter.1 he).2.trans (mem_filter.1 he').2.symm))
        hne.symm
      exact card_pos.2 ⟨z, (mem_neighborFinset _ _ _).2 hz⟩
    set K := LC.filter fun e => #((aux G M).neighborFinset e) = 1 with hK
    have hKcard : 2 ≤ #K := by
      by_contra hcon
      push Not at hcon
      have hge : ∀ e ∈ LC, (if e ∈ K then 1 else 2) ≤ #((aux G M).neighborFinset e) := by
        intro e he
        split_ifs with hk
        · exact hpos e he
        · have h1 := hpos e he
          have : #((aux G M).neighborFinset e) ≠ 1 := fun h => hk (mem_filter.2 ⟨he, h⟩)
          omega
      have hs := sum_le_sum hge
      have hKsub : K ⊆ LC := filter_subset _ _
      have hKsum : #K = ∑ e ∈ LC, (if e ∈ K then 1 else 0) := by
        rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.2 hKsub, card_eq_sum_ones]
      have hite : ∑ e ∈ LC, (if e ∈ K then 1 else 2) + #K = ∑ _e ∈ LC, 2 := by
        rw [hKsum, ← sum_add_distrib]
        exact sum_congr rfl fun e _ => by split_ifs <;> rfl
      rw [sum_const, smul_eq_mul] at hite
      omega
    obtain ⟨l₁, hl₁, l₂, hl₂, hne⟩ := one_lt_card.1 hKcard
    obtain ⟨hl₁L, hl₁d⟩ := mem_filter.1 hl₁
    obtain ⟨hl₂L, hl₂d⟩ := mem_filter.1 hl₂
    exact ⟨l₁, (mem_filter.1 hl₁L).1, l₂, (mem_filter.1 hl₂L).1, hne, (mem_filter.1 hl₁L).2,
      (mem_filter.1 hl₂L).2, hl₁d, hl₂d⟩
end MurtySimon
