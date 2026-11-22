-- Prove2me | solution 1 for MatchingLogic.BoxesControl.coord_arity_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:05.970264+00:00
-- url     : https://prove2.me/submissions/80cc19c6-f55d-4d58-b853-6fcb2a32b8bf

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Order.BooleanAlgebra.Set
public import Definitions.Def_LeanPool_MatchingLogic_BoxesControl

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.BoxesControl
namespace MatchingLogic.BoxesControl
theorem _root_.solution (S : Signature) (e : Coord S) : 1 ≤ S.arity e.1 := by
  have h := e.2.isLt
  omega
end MatchingLogic.BoxesControl
