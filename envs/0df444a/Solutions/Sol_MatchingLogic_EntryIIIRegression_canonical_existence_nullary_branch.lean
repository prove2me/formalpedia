-- Prove2me | solution 1 for MatchingLogic.EntryIIIRegression.canonical_existence_nullary_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:28.808719+00:00
-- url     : https://prove2.me/submissions/9e503b36-5f79-40d9-b526-4c4edc36999c

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
public import Theorems.Thm_MatchingLogic_canonicalExistence


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIIIRegression
open Set
attribute [local instance] MatchingLogic.EntryIIIRegression.instEncodableAuditSym
attribute [local instance] MatchingLogic.EntryIIIRegression.auditPatternCountable
namespace MatchingLogic.EntryIIIRegression
theorem _root_.solution
    (Gamma : CanonicalCarrier AuditSig)
    (happ : nullaryPattern ∈ Gamma.val) :
    ∃ components : Fin (AuditSig.arity AuditSym.nullary) → CanonicalCarrier AuditSig,
      (∀ i, (fun j : Fin (AuditSig.arity AuditSym.nullary) => Fin.elim0 j) i ∈
        (components i).val) ∧
      Gamma ∈ canonicalInterp AuditSym.nullary components :=
  canonicalExistence Gamma AuditSym.nullary (fun i => Fin.elim0 i) happ
end MatchingLogic.EntryIIIRegression
