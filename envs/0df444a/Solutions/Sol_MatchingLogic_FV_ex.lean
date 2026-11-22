-- Prove2me | solution 1 for MatchingLogic.FV_ex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:53.548605+00:00
-- url     : https://prove2.me/submissions/4199a9fc-b510-4a93-b363-bf3ca50a8cc1

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Semantics

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
omit [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution (x : Var) (φ : Pattern S Var) : FV (.ex x φ) = FV φ \ {x} := rfl
end MatchingLogic
