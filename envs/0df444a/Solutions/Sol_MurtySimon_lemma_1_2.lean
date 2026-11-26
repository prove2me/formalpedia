-- Prove2me | solution 1 for MurtySimon.lemma_1_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:22:39.214809+00:00
-- url     : https://prove2.me/submissions/c914ed55-ede8-4249-a04e-2da92ec0903d

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
public import Theorems.Thm_MurtySimon_card_sdiff_eq_card_Lt
public import Theorems.Thm_MurtySimon_card_compl_eq
public import Theorems.Thm_MurtySimon_IsDiameterTwoCritical_isCritical
public import Theorems.Thm_MurtySimon_card_Lt_le


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
namespace MurtySimon
theorem _root_.solution (hG : IsDiameterTwoCritical G) {M : Finset (Sym2 V)}
    (hM : IsMaximalEdgeMatching G M) : #(G.edgeFinset \ M) ≤ #Gᶜ.edgeFinset := by
  rw [card_sdiff_eq_card_Lt, card_compl_eq]
  exact card_Lt_le hM hG.isCritical
end MurtySimon
