-- Prove2me | solution 1 for MatchingLogic.strongLocalCompleteness_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:47:40.719803+00:00
-- url     : https://prove2.me/submissions/4999e12c-86ab-477c-b110-5e2c58fe50dd

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
public import Theorems.Thm_MatchingLogic_finiteLocalCompleteness
public import Theorems.Thm_MatchingLogic_strongLocalCompleteness_of_finiteLocalCompleteness


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
theorem _root_.solution : StrongLocalCompleteness S Nat :=
  strongLocalCompleteness_of_finiteLocalCompleteness finiteLocalCompleteness
end MatchingLogic
