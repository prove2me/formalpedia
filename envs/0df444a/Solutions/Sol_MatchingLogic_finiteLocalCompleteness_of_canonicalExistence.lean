-- Prove2me | solution 1 for MatchingLogic.finiteLocalCompleteness_of_canonicalExistence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:46.72833+00:00
-- url     : https://prove2.me/submissions/afdcafdd-209e-4e01-9a44-d0477dbefa40

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Truth
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_ModelExistence
public import Theorems.Thm_MatchingLogic_finiteLocalModelExistence_of_canonicalExistence
public import Theorems.Thm_MatchingLogic_finiteLocalCompleteness_of_finiteLocalModelExistence


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatModelExistence
namespace MatchingLogic
theorem _root_.solution
    [Countable (Pattern S Nat)] (hExist : CanonicalExistenceProperty S) :
    FiniteLocalCompleteness S Nat :=
  finiteLocalCompleteness_of_finiteLocalModelExistence
    (finiteLocalModelExistence_of_canonicalExistence hExist)
end MatchingLogic
