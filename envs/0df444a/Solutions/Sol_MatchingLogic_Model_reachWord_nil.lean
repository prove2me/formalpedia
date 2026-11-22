-- Prove2me | solution 1 for MatchingLogic.Model.reachWord_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:19.448968+00:00
-- url     : https://prove2.me/submissions/6e0b0f06-85be-4bdf-affe-ff27c57721a4

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
theorem _root_.solution (u v : M.carrier) : M.reachWord [] u v ↔ u = v := Iff.rfl
end MatchingLogic.Model
