-- Prove2me | solution 1 for MatchingLogic.Model.reachWord_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:20.054911+00:00
-- url     : https://prove2.me/submissions/355c8335-ee7d-4dd4-8251-fc1b8e213107

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
open MatchingLogic.Model
variable (M : Model S)
namespace MatchingLogic.Model
theorem _root_.solution (e : Coord S) (p : List (Coord S)) (u v : M.carrier) :
    M.reachWord (e :: p) u v ↔ ∃ w, M.stepAt e u w ∧ M.reachWord p w v := Iff.rfl
end MatchingLogic.Model
