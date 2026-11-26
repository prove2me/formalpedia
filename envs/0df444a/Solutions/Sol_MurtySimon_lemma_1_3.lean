-- Prove2me | solution 1 for MurtySimon.lemma_1_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:22:55.365554+00:00
-- url     : https://prove2.me/submissions/e03fa7ec-b6cc-423e-9487-7809f96d1584

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
public import Theorems.Thm_MurtySimon_card_sdiff_eq_card_Lt
public import Theorems.Thm_MurtySimon_card_compl_eq
public import Theorems.Thm_MurtySimon_IsDiameterTwoCritical_isCritical
public import Theorems.Thm_MurtySimon_cliqueFree_of_eqCase


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
namespace MurtySimon
theorem _root_.solution (hG : IsDiameterTwoCritical G)
    (heq : ∀ M, IsMaximalEdgeMatching G M → #(G.edgeFinset \ M) = #Gᶜ.edgeFinset) :
    G.CliqueFree 3 := by
  refine cliqueFree_of_eqCase hG.isCritical fun M hM => ?_
  rw [← card_sdiff_eq_card_Lt, ← card_compl_eq]
  exact heq M hM
end MurtySimon
