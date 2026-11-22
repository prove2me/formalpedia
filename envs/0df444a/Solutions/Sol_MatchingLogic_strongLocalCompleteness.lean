-- Prove2me | solution 1 for MatchingLogic.strongLocalCompleteness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:48:47.288238+00:00
-- url     : https://prove2.me/submissions/d1dc1914-d4e3-49f0-93ea-aab12015b8bb

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalConstruction
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_ModelExistence
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureReduction
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Theorems.Thm_MatchingLogic_strongLocalCompleteness_nat
public import Theorems.Thm_MatchingLogic_strongLocalCompleteness_iff_nat


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
theorem _root_.solution {Var : Type}
    [DecidableEq Var] [Denumerable Var] :
    StrongLocalCompleteness S Var :=
  (strongLocalCompleteness_iff_nat (S := S) (Var := Var)).mpr
    strongLocalCompleteness_nat
end MatchingLogic
