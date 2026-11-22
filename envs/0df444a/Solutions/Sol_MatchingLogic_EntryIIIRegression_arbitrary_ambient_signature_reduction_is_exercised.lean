-- Prove2me | solution 1 for MatchingLogic.EntryIIIRegression.arbitrary_ambient_signature_reduction_is_exercised
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:48:48.324093+00:00
-- url     : https://prove2.me/submissions/ffdadcd7-1e74-4870-a907-286a111f4402

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalConstruction
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Regression
public import Theorems.Thm_MatchingLogic_finiteLocalModelExistence
public import Theorems.Thm_MatchingLogic_strongLocalCompleteness_nat


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIIIRegression
open Set
attribute [local instance] MatchingLogic.EntryIIIRegression.instEncodableAuditSym
attribute [local instance] MatchingLogic.EntryIIIRegression.auditPatternCountable
namespace MatchingLogic.EntryIIIRegression
theorem _root_.solution :
    FiniteLocalModelExistence HugeSig Nat ∧
      StrongLocalCompleteness HugeSig Nat :=
  ⟨finiteLocalModelExistence, strongLocalCompleteness_nat⟩
end MatchingLogic.EntryIIIRegression
