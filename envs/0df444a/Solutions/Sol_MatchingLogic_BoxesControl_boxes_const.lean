-- Prove2me | solution 1 for MatchingLogic.BoxesControl.boxes_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:13.82043+00:00
-- url     : https://prove2.me/submissions/280718ab-1b15-427f-9e9c-c3c19a87cd81

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
theorem _root_.solution (p : List (Coord SgConst)) (ψ : Pattern SgConst Nat) :
    boxes p ψ = ψ := by
  induction p with
  | nil => rfl
  | cons e p _ => exact Fin.elim0 e.2
end MatchingLogic.BoxesControl
