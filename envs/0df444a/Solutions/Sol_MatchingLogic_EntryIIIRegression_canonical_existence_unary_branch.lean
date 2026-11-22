-- Prove2me | solution 1 for MatchingLogic.EntryIIIRegression.canonical_existence_unary_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:35.338405+00:00
-- url     : https://prove2.me/submissions/2eb7ea2d-025c-43a6-bba5-cf2ce63e12e0

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
    (happ : unaryPattern ∈ Gamma.val) :
    ∃ components : Fin (AuditSig.arity AuditSym.unary) → CanonicalCarrier AuditSig,
      (∀ i, (Pattern.var 0 : Pattern AuditSig Nat) ∈ (components i).val) ∧
      Gamma ∈ canonicalInterp AuditSym.unary components :=
  canonicalExistence Gamma AuditSym.unary (fun _ => .var 0) happ
end MatchingLogic.EntryIIIRegression
