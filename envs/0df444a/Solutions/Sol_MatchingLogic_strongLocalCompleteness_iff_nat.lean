-- Prove2me | solution 1 for MatchingLogic.strongLocalCompleteness_iff_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:46.217215+00:00
-- url     : https://prove2.me/submissions/74fe49bd-9438-48de-a77b-96c29d8d5200

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Theorems.Thm_MatchingLogic_strongLocalCompleteness_congr

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
namespace MatchingLogic
theorem _root_.solution [DecidableEq Var] [Denumerable Var] :
    StrongLocalCompleteness S Var ↔ StrongLocalCompleteness S Nat := by
  exact strongLocalCompleteness_congr (Denumerable.eqv Var)
end MatchingLogic
