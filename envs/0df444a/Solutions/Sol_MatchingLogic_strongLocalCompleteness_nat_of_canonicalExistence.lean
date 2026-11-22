-- Prove2me | solution 1 for MatchingLogic.strongLocalCompleteness_nat_of_canonicalExistence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:07.805981+00:00
-- url     : https://prove2.me/submissions/ea72288d-e8ef-4ab7-adf2-e035440ddaf7

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Truth
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_ModelExistence
public import Theorems.Thm_MatchingLogic_finiteLocalCompleteness_of_canonicalExistence
public import Theorems.Thm_MatchingLogic_strongLocalCompleteness_of_finiteLocalCompleteness


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
    StrongLocalCompleteness S Nat :=
  strongLocalCompleteness_of_finiteLocalCompleteness
    (finiteLocalCompleteness_of_canonicalExistence hExist)
end MatchingLogic
