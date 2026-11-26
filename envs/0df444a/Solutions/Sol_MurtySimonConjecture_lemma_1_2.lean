-- Prove2me | solution 1 for MurtySimonConjecture.lemma_1_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:25:59.161097+00:00
-- url     : https://prove2.me/submissions/51cd221e-54eb-4bef-b745-a0191b009a30

module
public import Definitions.Def_MurtySimon_Main
public import Definitions.Def_MurtySimon_Solution
public import Theorems.Thm_MurtySimon_lemma_1_2


set_option autoImplicit true
@[expose] public section
public section
open MurtySimonConjecture
open Finset SimpleGraph
variable {V : Type*}
namespace MurtySimonConjecture
theorem _root_.solution [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsDiameterTwoCritical G) (M : Finset (Sym2 V)) (hM : IsMaximalEdgeMatching G M) :
    #(G.edgeFinset \ M) ≤ #Gᶜ.edgeFinset :=
  MurtySimon.lemma_1_2 hG hM
end MurtySimonConjecture
