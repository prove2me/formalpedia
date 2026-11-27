-- Prove2me | solution 1 for MatchingPolytope.Multi.inHull_of_reducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:33:16.59643+00:00
-- url     : https://prove2.me/submissions/68d95e09-66ff-4f30-9bf6-b698284389da

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
public import Theorems.Thm_MatchingPolytope_Multi_odd_card_sdiff
public import Theorems.Thm_MatchingPolytope_Multi_mem_poly_erase
public import Theorems.Thm_MatchingPolytope_Multi_InHull_mono
public import Theorems.Thm_MatchingPolytope_Multi_Valid_mono
public import Theorems.Thm_MatchingPolytope_Multi_card_shrinkW_lt
public import Theorems.Thm_MatchingPolytope_Multi_even_card_of_mem_poly
public import Theorems.Thm_MatchingPolytope_Multi_gcut_compl
public import Theorems.Thm_MatchingPolytope_Multi_inHull_glue
public import Theorems.Thm_MatchingPolytope_Multi_restr_mem_poly_shrink
public import Theorems.Thm_MatchingPolytope_Multi_shrinkF_subset
public import Theorems.Thm_MatchingPolytope_Multi_shrink_valid


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution [DecidableEq V] [Fintype E]
    (IH : ∀ (ends' : E → Sym2 V) (W' : Finset V) (F' : Finset E),
      W'.card + F'.card < W.card + F.card → Valid ends' W' F' →
        ∀ x ∈ Poly ends' W' F', InHull (IsPM ends' W' F') x)
    (hV : Valid ends W F) {y : E → ℝ} (hy : y ∈ Poly ends W F) (hr : Reducible ends W F y) :
    InHull (IsPM ends W F) y := by
  classical
  by_cases h0 : ∃ e ∈ F, y e = 0
  · obtain ⟨e, he, he0⟩ := h0
    have hlt : W.card + (F.erase e).card < W.card + F.card := by
      have := Finset.card_erase_lt_of_mem he
      omega
    have := IH ends W (F.erase e) hlt (hV.mono (Finset.erase_subset _ _)) y
      (mem_poly_erase hy he0)
    exact this.mono fun M hM => ⟨hM.1.trans (Finset.erase_subset _ _), hM.2⟩
  · have hpos : ∀ e ∈ F, 0 < y e := by
      intro e he
      refine lt_of_le_of_ne (hy.2.1 e) ?_
      intro h
      exact h0 ⟨e, he, h.symm⟩
    obtain ⟨S, hSW, hSodd, hS1, hWS1, htight⟩ := hr.resolve_left h0
    have hW := even_card_of_mem_poly hV hy
    obtain ⟨s, hs⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨t, ht⟩ : (W \ S).Nonempty := Finset.card_pos.1 (by omega)
    have hWSodd := odd_card_sdiff hSW hW hSodd
    have hS' : W \ S ⊆ W := Finset.sdiff_subset
    apply inHull_glue hV hy hpos hSW hs ht
    · apply IH _ _ _ _ (shrink_valid hV hs) _ (restr_mem_poly_shrink hV hy hSW hs hSodd htight)
      have := card_shrinkW_lt hSW hS1 s
      have := Finset.card_le_card (shrinkF_subset (ends := ends) (F := F) S)
      omega
    · apply IH _ _ _ _ (shrink_valid hV ht) _
        (restr_mem_poly_shrink hV hy hS' ht hWSodd (by rwa [gcut_compl hV subset_rfl]))
      have := card_shrinkW_lt hS' hWS1 t
      have := Finset.card_le_card (shrinkF_subset (ends := ends) (F := F) (W \ S))
      omega
end MatchingPolytope.Multi
