-- Prove2me | solution 1 for MurtySimonConjecture.murty_simon_equality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:29:12.883665+00:00
-- url     : https://prove2.me/submissions/a9a0f583-fc31-4f74-8469-1994ba8b70d7

module
public import Definitions.Def_MurtySimon_Main
public import Definitions.Def_MurtySimon_Solution
public import Theorems.Thm_MurtySimon_nonempty_iso_completeBipartiteGraph


set_option autoImplicit true
@[expose] public section
public section
open MurtySimonConjecture
open Finset SimpleGraph
variable {V : Type*}
namespace MurtySimonConjecture
theorem _root_.solution [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsDiameterTwoCritical G)
    (hE : #G.edgeFinset = Fintype.card V ^ 2 / 4) :
    Nonempty (G ≃g completeBipartiteGraph (Fin ((Fintype.card V + 1) / 2))
      (Fin (Fintype.card V / 2))) :=
  MurtySimon.nonempty_iso_completeBipartiteGraph hG hE
end MurtySimonConjecture
