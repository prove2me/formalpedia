-- Prove2me | solution 1 for LeanPool.Vizing.PEC.kempeSwap_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:54:06.95662+00:00
-- url     : https://prove2.me/submissions/556cc59c-2ce4-460f-bd87-28302ccfe272

module
public import Definitions.Def_LeanPool_Vizing_Endpoints
public import Definitions.Def_LeanPool_Vizing_Kempe

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}
omit [Fintype V] [DecidableEq V]
namespace LeanPool.Vizing.PEC
theorem _root_.solution (c : PEC G C) (a b : C) (x : V) :
    (c.kempeSwap a b x).col = c.kempeSwapFun a b x := rfl
end LeanPool.Vizing.PEC
