-- Prove2me | solution 1 for NashWilliams.exists_trees_of_isEdgeConnected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:34:15.266739+00:00
-- url     : https://prove2.me/submissions/e488284e-3c27-4acb-b3ef-02cf4fd71ed1

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Definitions.Def_TreePackingLib_NashWilliams
public import Theorems.Thm_NashWilliams_tree_packing
public import Theorems.Thm_NashWilliams_reachable_closed


set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph
open NashWilliams
namespace NashWilliams
theorem _root_.solution {V : Type*} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (k : ℕ) (hG : G.IsEdgeConnected (2 * k)) :
    ∃ T : Fin k → SimpleGraph V, (∀ i, T i ≤ G ∧ (T i).IsTree) ∧
      Pairwise fun i j ↦ Disjoint (T i) (T j) := by
  have := Fintype.ofFinite V
  classical
  refine (tree_packing G k).2 fun f ↦ ?_
  by_cases hm : #(univ.image f) ≤ 1
  · simp [Nat.sub_eq_zero_of_le hm]
  push Not at hm
  set K := G ⊓ (⊤ : SimpleGraph V).comap f
  have hfib : ∀ r ∈ univ.image f, 2 * k ≤ #(univ.filter fun d : K.Dart ↦ f d.fst = r) := by
    intro r hr
    obtain ⟨x, -, hx⟩ := mem_image.1 hr
    obtain ⟨r', hr', hr'r⟩ := exists_mem_ne hm r
    obtain ⟨y, -, hy⟩ := mem_image.1 hr'
    by_contra hlt
    push Not at hlt
    set s : Set (Sym2 V) :=
      ↑((univ.filter fun d : K.Dart ↦ f d.fst = r).image Dart.edge)
    have hs : s.encard < (2 * k : ℕ) := by
      rw [Set.encard_coe_eq_coe_finsetCard]
      exact_mod_cast card_image_le.trans_lt hlt
    have hreach := hG x y hs
    have : f y = r := reachable_closed (fun w ↦ f w = r) (fun a b hab ha ↦ by
      by_contra hb
      rw [deleteEdges_adj] at hab
      refine hab.2 ?_
      have hK : K.Adj a b := ⟨hab.1, by simp [ha, Ne.symm hb]⟩
      exact mem_image.2 ⟨⟨(a, b), hK⟩, by simp [ha], rfl⟩) hreach hx
    exact hr'r (hy.symm.trans this)
  have hdart : Fintype.card K.Dart =
      ∑ r ∈ univ.image f, #(univ.filter fun d : K.Dart ↦ f d.fst = r) :=
    card_eq_sum_card_fiberwise fun d _ ↦ mem_image_of_mem _ (mem_univ _)
  have hsum : ∑ _r ∈ univ.image f, 2 * k ≤
      ∑ r ∈ univ.image f, #(univ.filter fun d : K.Dart ↦ f d.fst = r) :=
    sum_le_sum hfib
  have h2 := K.dart_card_eq_twice_card_edges
  simp only [edgeFinset_card, Fintype.card_eq_nat_card, Nat.card_coe_set_eq] at h2 hdart
  rw [h2] at hdart
  rw [sum_const, smul_eq_mul, ← hdart] at hsum
  have : k * (#(univ.image f) - 1) ≤ k * #(univ.image f) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  nlinarith
end NashWilliams
