-- Prove2me | solution 1 for MurtySimonConjecture.lemma_1_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:26:02.623993+00:00
-- url     : https://prove2.me/submissions/42f52a6a-99b3-478a-9384-7ed3f981db14

module
public import Definitions.Def_MurtySimon_Main
public import Definitions.Def_MurtySimon_Solution
public import Theorems.Thm_MurtySimon_lemma_1_3


set_option autoImplicit true
@[expose] public section
public section
open MurtySimonConjecture
open Finset SimpleGraph
variable {V : Type*}
namespace MurtySimonConjecture
theorem _root_.solution [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsDiameterTwoCritical G)
    (heq : ∀ M, IsMaximalEdgeMatching G M → #(G.edgeFinset \ M) = #Gᶜ.edgeFinset) :
    G.CliqueFree 3 :=
  MurtySimon.lemma_1_3 hG heq
end MurtySimonConjecture
