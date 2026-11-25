-- Prove2me | solution 1 for Menger.isEdgeReachable_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:20:32.027801+00:00
-- url     : https://prove2.me/submissions/b228b6c2-d93e-40a5-a658-094f71f79bd5

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
public import Definitions.Def_MengerHamilton_Menger
public import Theorems.Thm_Menger_exists_separator_and_paths
public import Theorems.Thm_Menger_Aux_lift_to_lineGraph
public import Theorems.Thm_Menger_Aux_lower_from_lineGraph


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger
variable {V : Type*}
namespace Menger
theorem _root_.solution [Finite V] (G : SimpleGraph V) (k : ℕ) (u v : V) :
    G.IsEdgeReachable k u v ↔
      ∃ p : Fin k → G.Walk u v, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → (p i).edges.Disjoint (p j).edges := by
  constructor
  · intro h
    by_cases huv : u = v
    · subst huv
      exact ⟨fun _ => Walk.nil, fun _ => Walk.IsPath.nil, fun _ _ _ => by simp⟩
    classical
    have := Fintype.ofFinite V
    obtain ⟨X, hX, a, b, P, hP, hd⟩ := exists_separator_and_paths G.lineGraph
      (Finset.univ.filter (fun e : G.edgeSet => u ∈ (e : Sym2 V)))
      (Finset.univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V)))
    have hk : k ≤ X.card := by
      by_contra hlt
      push Not at hlt
      have hS : (Subtype.val '' (X : Set G.edgeSet)).encard < k := by
        rw [Subtype.val_injective.encard_image, Set.encard_coe_eq_coe_finsetCard]
        exact_mod_cast hlt
      obtain ⟨q⟩ := h hS
      obtain ⟨w, hadj, q', -⟩ := Walk.exists_eq_cons_of_ne huv q
      rw [deleteEdges_adj] at hadj
      obtain ⟨e', he'v, r, hr⟩ := Aux.lift_to_lineGraph (q'.mapLe (G.deleteEdges_le _))
        ⟨s(u, w), hadj.1⟩ (Sym2.mem_mk_right _ _)
      obtain ⟨x, hxX, hxr⟩ := hX ⟨s(u, w), hadj.1⟩ (by simp) e' (by simp [he'v]) r
      rcases hr x hxr with rfl | hx
      · exact hadj.2 ⟨_, hxX, rfl⟩
      · rw [Walk.edges_mapLe_eq_edges] at hx
        have := q'.edges_subset_edgeSet hx
        rw [edgeSet_deleteEdges] at this
        exact this.2 ⟨x, hxX, rfl⟩
    have hlow : ∀ i, ∃ r : G.Walk u v, ∀ g ∈ r.edges, ∃ e'' ∈ (P i).support, g = (e'' : Sym2 V) :=
      fun i => Aux.lower_from_lineGraph (P i) (by simpa using (hP i).1) (by simpa using (hP i).2.1)
    choose r hr using hlow
    refine ⟨fun i => (r (Fin.castLE hk i)).bypass, fun i => Walk.bypass_isPath _,
      fun i j hij g hg hg' => ?_⟩
    obtain ⟨e1, he1, rfl⟩ := hr _ g (Walk.edges_bypass_subset_edges _ hg)
    obtain ⟨e2, he2, he12⟩ := hr _ _ (Walk.edges_bypass_subset_edges _ hg')
    have := Subtype.ext he12
    subst this
    exact hd _ _ (fun h => hij (Fin.castLE_injective hk h)) _ he1 he2
  · rintro ⟨p, hp, hd⟩ S hS
    by_contra hreach
    have hmeet : ∀ i, ∃ e ∈ (p i).edges, e ∈ S := by
      intro i
      by_contra h
      push Not at h
      exact hreach ⟨(p i).toDeleteEdges S h⟩
    choose f hf hfS using hmeet
    have hinj : Set.InjOn f Set.univ := by
      intro i _ j _ hij
      by_contra hne
      exact hd i j hne (hf i) (by rw [hij]; exact hf j)
    have := Set.encard_le_encard_of_injOn (fun i _ => hfS i) hinj
    simp only [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] at this
    exact absurd hS (not_lt.2 this)
end Menger
