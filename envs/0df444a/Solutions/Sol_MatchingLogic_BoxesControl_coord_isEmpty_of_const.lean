-- Prove2me | solution 1 for MatchingLogic.BoxesControl.coord_isEmpty_of_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:13.369773+00:00
-- url     : https://prove2.me/submissions/fad71b51-98c9-4377-80f1-0263024a1a46

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
theorem _root_.solution : IsEmpty (Coord SgConst) := by
  constructor
  intro e
  exact Fin.elim0 e.2
end MatchingLogic.BoxesControl
