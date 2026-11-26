-- Prove2me | solution 1 for MurtySimonConjecture.murty_simon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:27:42.725979+00:00
-- url     : https://prove2.me/submissions/0d343730-b776-4600-80dc-0fcb9a98731b

module
public import Definitions.Def_MurtySimon_Main
public import Definitions.Def_MurtySimon_Solution
public import Theorems.Thm_MurtySimon_card_edgeFinset_le


set_option autoImplicit true
@[expose] public section
public section
open MurtySimonConjecture
open Finset SimpleGraph
variable {V : Type*}
namespace MurtySimonConjecture
theorem _root_.solution [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsDiameterTwoCritical G) : #G.edgeFinset ≤ Fintype.card V ^ 2 / 4 :=
  MurtySimon.card_edgeFinset_le hG
end MurtySimonConjecture
