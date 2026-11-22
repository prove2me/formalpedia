-- Prove2me | solution 1 for MatchingLogic.finiteLocalCompleteness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:49.79029+00:00
-- url     : https://prove2.me/submissions/68232962-6d9a-4f5b-967b-e363f1fe9994

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
public import Theorems.Thm_MatchingLogic_finiteLocalModelExistence
public import Theorems.Thm_MatchingLogic_finiteLocalCompleteness_of_finiteLocalModelExistence


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
theorem _root_.solution : FiniteLocalCompleteness S Nat :=
  finiteLocalCompleteness_of_finiteLocalModelExistence finiteLocalModelExistence
end MatchingLogic
