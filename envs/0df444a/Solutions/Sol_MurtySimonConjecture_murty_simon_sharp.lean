-- Prove2me | solution 1 for MurtySimonConjecture.murty_simon_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:25:48.762837+00:00
-- url     : https://prove2.me/submissions/1fb1993b-1238-4228-91b4-df1556dcb9b3

module
public import Definitions.Def_MurtySimon_Main
public import Definitions.Def_MurtySimon_Solution
public import Theorems.Thm_MurtySimon_card_edgeSet_completeBipartiteGraph
public import Theorems.Thm_MurtySimon_completeBipartiteGraph_isDiameterTwoCritical


set_option autoImplicit true
@[expose] public section
public section
open MurtySimonConjecture
open Finset SimpleGraph
variable {V : Type*}
namespace MurtySimonConjecture
theorem _root_.solution (n : ℕ) (hn : 3 ≤ n) :
    IsDiameterTwoCritical (completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))) ∧
      Nat.card (completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))).edgeSet =
        n ^ 2 / 4 :=
  ⟨MurtySimon.completeBipartiteGraph_isDiameterTwoCritical hn,
    MurtySimon.card_edgeSet_completeBipartiteGraph n⟩
end MurtySimonConjecture
