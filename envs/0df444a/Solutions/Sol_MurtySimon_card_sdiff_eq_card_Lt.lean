-- Prove2me | solution 1 for MurtySimon.card_sdiff_eq_card_Lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:20:50.936413+00:00
-- url     : https://prove2.me/submissions/78a9463b-640c-49fb-abd2-e575b79e1814

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
public import Theorems.Thm_MurtySimon_mem_Lt


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
namespace MurtySimon
theorem _root_.solution (M : Finset (Sym2 V)) : #(G.edgeFinset \ M) = #(Lt G M) := by
  congr 1; ext e; simp [mem_Lt]
end MurtySimon
