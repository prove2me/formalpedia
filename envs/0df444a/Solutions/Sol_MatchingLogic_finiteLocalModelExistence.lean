-- Prove2me | solution 1 for MatchingLogic.finiteLocalModelExistence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:58.232925+00:00
-- url     : https://prove2.me/submissions/dfde35fe-02f0-4759-8729-b59cc44a39e9

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
public import Theorems.Thm_MatchingLogic_canonicalExistence
public import Theorems.Thm_MatchingLogic_finiteLocalModelExistence_of_canonicalExistence
public import Theorems.Thm_MatchingLogic_finiteLocalModelExistence_of_restricted
public import Theorems.Thm_MatchingLogic_restrictedPatternNatCountable


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
theorem _root_.solution : FiniteLocalModelExistence S Nat := by
  classical
  apply finiteLocalModelExistence_of_restricted
  intro F
  have : Countable (Pattern (S.restrict F) Nat) :=
    restrictedPatternNatCountable F
  exact finiteLocalModelExistence_of_canonicalExistence canonicalExistence
end MatchingLogic
