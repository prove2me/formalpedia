-- Prove2me | solution 1 for MatchingLogic.AppCtx.plug_liftSignature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:42.8058+00:00
-- url     : https://prove2.me/submissions/4e3f807f-113b-4c77-9144-bdeb5375b3cc

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Theorems.Thm_MatchingLogic_Pattern_liftSignature_update

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
open MatchingLogic.AppCtx
omit [DecidableEq Var]
namespace MatchingLogic.AppCtx
theorem _root_.solution [DecidableEq S.Sym] (F : Finset S.Sym)
    (C : AppCtx (S.restrict F) Var) (p : Pattern (S.restrict F) Var) :
    (C.plug p).liftSignature F = (C.liftSignature F).plug (p.liftSignature F) := by
  induction C with
  | hole => rfl
  | node sigma i args C ih =>
      have hupdate := Pattern.liftSignature_update F args i (C.plug p)
      rw [ih] at hupdate
      exact congrArg (Pattern.app sigma.1) hupdate
end MatchingLogic.AppCtx
