-- Prove2me | solution 1 for GridHam.nodup_remove_mid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:40:07.24132+00:00
-- url     : https://prove2.me/submissions/a6372135-80fc-4e80-bc17-8e81c1232a82

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_P2M_GridHam_nodup_append_right__a582c6ad4e63
public import Theorems.Thm_GridHam_nodup_append_disjoint
public import Theorems.Thm_GridHam_mem_insert_iff


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ (L : List Coord) (a b : Coord) (M R : List Coord),
    (L ++ a :: (M ++ b :: R)).Nodup →
    (L ++ a :: b :: R).Nodup ∧ ∀ c ∈ M, c ∉ L ++ a :: b :: R := by
  intro L
  induction L with
  | nil =>
    intro a b M R h
    have h' : (a :: (M ++ b :: R)).Nodup := h
    obtain ⟨han, hrest⟩ := List.nodup_cons.mp h'
    have hbr := nodup_append_right' M (b :: R) hrest
    have hdis := nodup_append_disjoint M (b :: R) hrest
    refine ⟨?_, ?_⟩
    · show (a :: b :: R).Nodup
      rw [List.nodup_cons]
      exact ⟨fun hm => han (List.mem_append.mpr (Or.inr hm)), hbr⟩
    · intro c hc hcq
      have hcq' : c ∈ a :: b :: R := hcq
      rcases List.mem_cons.mp hcq' with e | e
      · rw [e] at hc
        exact han (List.mem_append.mpr (Or.inl hc))
      · exact hdis c hc e
  | cons x L ih =>
    intro a b M R h
    have h' : (x :: (L ++ a :: (M ++ b :: R))).Nodup := h
    obtain ⟨hxn, hrest⟩ := List.nodup_cons.mp h'
    obtain ⟨hq, hd⟩ := ih a b M R hrest
    refine ⟨?_, ?_⟩
    · show (x :: (L ++ a :: b :: R)).Nodup
      rw [List.nodup_cons]
      exact ⟨fun hm => hxn ((mem_insert_iff x L M R a b).mpr (Or.inr hm)), hq⟩
    · intro c hc hcq
      have hcq' : c ∈ x :: (L ++ a :: b :: R) := hcq
      rcases List.mem_cons.mp hcq' with e | e
      · rw [e] at hc
        exact hxn ((mem_insert_iff x L M R a b).mpr (Or.inl hc))
      · exact hd c hc e
end GridHam
