-- Prove2me | solution 1 for MurtySimon.two_mul_card_le_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:25:21.001193+00:00
-- url     : https://prove2.me/submissions/2968fbc6-6c19-4953-939b-7793e21bbcdc

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
public import Theorems.Thm_MurtySimon_card_add_card_compl
public import Theorems.Thm_MurtySimon_lemma_1_2

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
namespace MurtySimon
theorem _root_.solution (hG : IsDiameterTwoCritical G) {M : Finset (Sym2 V)}
    (hM : IsMaximalEdgeMatching G M) :
    2 * #G.edgeFinset ≤ (Fintype.card V).choose 2 + #M := by
  have h1 := lemma_1_2 hG hM
  have h2 := card_add_card_compl G
  have hsub : M ⊆ G.edgeFinset := fun e he => mem_edgeFinset.2 (hM.1.1 e he)
  have h3 := card_sdiff_add_card_inter G.edgeFinset M
  rw [inter_eq_right.2 hsub] at h3
  omega
end MurtySimon
