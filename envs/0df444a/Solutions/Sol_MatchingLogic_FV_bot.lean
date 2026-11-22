-- Prove2me | solution 1 for MatchingLogic.FV_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:51.928419+00:00
-- url     : https://prove2.me/submissions/76d3946d-4e40-46e0-8197-aba75c2169c2

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
theorem _root_.solution : FV (.bot : Pattern S Var) = ∅ := rfl
end MatchingLogic
