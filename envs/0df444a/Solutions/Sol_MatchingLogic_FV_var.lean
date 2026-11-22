-- Prove2me | solution 1 for MatchingLogic.FV_var
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:51.470804+00:00
-- url     : https://prove2.me/submissions/3fbf9541-b638-4198-9d00-ca765eab67e6

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
theorem _root_.solution (x : Var) : FV (.var x : Pattern S Var) = {x} := rfl
end MatchingLogic
