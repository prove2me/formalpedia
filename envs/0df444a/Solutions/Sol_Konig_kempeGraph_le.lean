-- Prove2me | solution 1 for Konig.kempeGraph_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:34:23.448857+00:00
-- url     : https://prove2.me/submissions/95d05f3b-d330-4e4c-bd33-03329dcde7ec

module
public import Definitions.Def_LeanPool_Vizing_Main
public import Definitions.Def_Konig_Basic

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Konig
open LeanPool.Vizing LeanPool.Vizing.PEC
variable {V : Type*} {C : Type*} {G : SimpleGraph V}
namespace Konig
theorem _root_.solution (c : PEC G C) (a b : C) : c.kempeGraph a b ≤ G := by
  intro u v h
  rcases h.2 with h | h <;> exact c.col_adj h
end Konig
