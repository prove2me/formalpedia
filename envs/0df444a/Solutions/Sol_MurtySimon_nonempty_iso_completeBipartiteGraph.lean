-- Prove2me | solution 1 for MurtySimon.nonempty_iso_completeBipartiteGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:27:41.889871+00:00
-- url     : https://prove2.me/submissions/d690a0b9-2082-4d68-a53a-28138eb1972e

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
public import Theorems.Thm_MurtySimon_two_mul_card_le
public import Theorems.Thm_MurtySimon_choose_two_add_half
public import Theorems.Thm_MurtySimon_card_add_card_compl
public import Theorems.Thm_MurtySimon_lemma_1_2
public import Theorems.Thm_MurtySimon_lemma_1_3
public import Theorems.Thm_MurtySimon_card_edgeFinset_le

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
namespace MurtySimon
theorem _root_.solution (hG : IsDiameterTwoCritical G)
    (hE : #G.edgeFinset = Fintype.card V ^ 2 / 4) :
    Nonempty (G ≃g completeBipartiteGraph (Fin ((Fintype.card V + 1) / 2))
      (Fin (Fintype.card V / 2))) := by
  have hcf : G.CliqueFree 3 := by
    apply lemma_1_3 hG
    intro M hM
    have h1 := lemma_1_2 hG hM
    have h2 := card_add_card_compl G
    have h3 := two_mul_card_le hM.1
    have h4 := choose_two_add_half (Fintype.card V)
    have hsub : M ⊆ G.edgeFinset := fun e he => mem_edgeFinset.2 (hM.1.1 e he)
    have h5 := card_sdiff_add_card_inter G.edgeFinset M
    rw [inter_eq_right.2 hsub] at h5
    omega
  have hT : G.IsTuranMaximal 2 := by
    refine ⟨hcf, fun H _ hH => ?_⟩
    have hmod : Fintype.card V % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hch : (Fintype.card V % 2).choose 2 = 0 := Nat.choose_eq_zero_of_lt hmod
    rw [hE]
    refine (hH.card_edgeFinset_le).trans ?_
    rw [hch, add_zero, show 2 - 1 = 1 by rfl, mul_one, show 2 * 2 = 4 by rfl]
    exact Nat.div_le_div_right (Nat.sub_le _ _)
  obtain ⟨e⟩ := (isTuranMaximal_iff_nonempty_iso_turanGraph (by norm_num)).1 hT
  exact ⟨e.trans (turanIso _)⟩
end MurtySimon
