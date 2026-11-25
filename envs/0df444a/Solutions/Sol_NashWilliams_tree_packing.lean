-- Prove2me | solution 1 for NashWilliams.tree_packing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:29:22.844231+00:00
-- url     : https://prove2.me/submissions/9455e4e1-ad30-4f3f-9a31-74b1bdb68e73

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Definitions.Def_TreePackingLib_NashWilliams
public import Theorems.Thm_NashWilliams_IsAcyclic_ncard_edgeSet_add_one_le
public import Theorems.Thm_NashWilliams_card_image_le_ncard_crossing_add_one
public import Theorems.Thm_NashWilliams_card_le_ncard_edgeSet_add_card_image
public import Theorems.Thm_NashWilliams_exists_forests_core
public import Theorems.Thm_NashWilliams_sum_ncard_le_of_pairwise_disjoint


set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph
open NashWilliams
namespace NashWilliams
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    (k : ℕ) :
    (∃ T : Fin k → SimpleGraph V, (∀ i, T i ≤ G ∧ (T i).IsTree) ∧
        Pairwise fun i j ↦ Disjoint (T i) (T j)) ↔
      ∀ f : V → V,
        k * (#(univ.image f) - 1) ≤ (G ⊓ (⊤ : SimpleGraph V).comap f).edgeSet.ncard := by
  constructor
  · rintro ⟨T, hT, hdisj⟩ f
    have h1 : ∀ i, #(univ.image f) - 1 ≤ ((T i).edgeSet ∩ ((⊤ : SimpleGraph V).comap f).edgeSet).ncard := fun i ↦ by
      have := card_image_le_ncard_crossing_add_one (hT i).2.connected f
      omega
    have h2 := sum_ncard_le_of_pairwise_disjoint
      (fun i ↦ (T i).edgeSet ∩ ((⊤ : SimpleGraph V).comap f).edgeSet)
      (G ⊓ (⊤ : SimpleGraph V).comap f).edgeSet
      (fun i ↦ by rw [edgeSet_inf]; exact Set.inter_subset_inter_left _ (edgeSet_mono (hT i).1))
      (fun i j hij ↦ (disjoint_edgeSet.2 (hdisj hij)).mono Set.inter_subset_left
        Set.inter_subset_left)
    calc k * (#(univ.image f) - 1) = ∑ _i : Fin k, (#(univ.image f) - 1) := by simp
      _ ≤ ∑ i, ((T i).edgeSet ∩ ((⊤ : SimpleGraph V).comap f).edgeSet).ncard :=
          sum_le_sum fun i _ ↦ h1 i
      _ ≤ _ := h2
  · intro hcond
    obtain ⟨F, H, hF, hdisj, -, hreach, hcov⟩ := exists_forests_core G k
    refine ⟨F, fun i ↦ ⟨(hF i).1, ?_⟩, hdisj⟩
    let f : V → V := fun v ↦ Quot.out (H.connectedComponentMk v)
    have hfr : ∀ v, H.Reachable v (f v) := fun v ↦
      (ConnectedComponent.exact (Quot.out_eq (H.connectedComponentMk v))).symm
    have hfeq : ∀ a b, H.Adj a b → f a = f b := fun a b hab ↦ by
      simp only [f, ConnectedComponent.sound hab.reachable]
    have hcf := hcond f
    set m := #(univ.image f)
    set C := (G ⊓ (⊤ : SimpleGraph V).comap f).edgeSet
    have hC : C ⊆ ⋃ j, (F j).edgeSet ∩ C := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        have he' : G.Adj a b ∧ f a ≠ f b := by simpa [C] using he
        obtain ⟨j, hj⟩ := hcov a b he'.1 fun h ↦ he'.2 (hfeq a b h)
        exact Set.mem_iUnion.2 ⟨j, hj, he⟩
    have hsum : C.ncard ≤ ∑ j, ((F j).edgeSet ∩ C).ncard :=
      (Set.ncard_le_ncard hC (Set.toFinite _)).trans (Set.ncard_iUnion_le_of_fintype _)
    have hbound : ∀ j, ((F j).edgeSet ∩ C).ncard + Nat.card V ≤
        (F j).edgeSet.ncard + m := by
      intro j
      have hLB := card_le_ncard_edgeSet_add_card_image (F j ⊓ H) f
        fun v ↦ hreach j _ _ (hfr v)
      have hdj : Disjoint ((F j).edgeSet ∩ C) (F j ⊓ H).edgeSet := by
        rw [Set.disjoint_left]
        intro e he he'
        induction e using Sym2.ind with
        | _ a b =>
          have h1 : G.Adj a b ∧ f a ≠ f b := by simpa [C] using he.2
          exact h1.2 (hfeq a b he'.2)
      have hsub : (F j).edgeSet ∩ C ∪ (F j ⊓ H).edgeSet ⊆ (F j).edgeSet :=
        Set.union_subset Set.inter_subset_left (edgeSet_mono inf_le_left)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_union_eq hdj (Set.toFinite _) (Set.toFinite _)] at this
      omega
    by_contra hnt
    have hlt : ∑ j, ((F j).edgeSet ∩ C).ncard < ∑ _j : Fin k, (m - 1) := by
      refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, mem_univ i, ?_⟩
      · have := (IsAcyclic.ncard_edgeSet_add_one_le (hF j).2).1
        have := hbound j
        omega
      · have h1 := IsAcyclic.ncard_edgeSet_add_one_le (hF i).2
        have h2 : ¬ Nat.card V ≤ (F i).edgeSet.ncard + 1 := fun h ↦ hnt (h1.2 h)
        have := hbound i
        omega
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hlt
    omega
end NashWilliams
