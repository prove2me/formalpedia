-- Prove2me | solution 1 for MatchingLogic.boxes_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:18.692223+00:00
-- url     : https://prove2.me/submissions/824ae3f0-636b-410e-acc4-f42b1e7924b5

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Logic.Relation
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Boxes

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type}
namespace MatchingLogic
theorem _root_.solution (e : Coord S) (p : List (Coord S)) (ψ : Pattern S Var) :
    boxes (e :: p) ψ = box e (boxes p ψ) := rfl
end MatchingLogic
