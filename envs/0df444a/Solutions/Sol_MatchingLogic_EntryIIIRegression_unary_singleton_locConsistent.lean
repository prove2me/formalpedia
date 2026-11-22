-- Prove2me | solution 1 for MatchingLogic.EntryIIIRegression.unary_singleton_locConsistent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:49.566372+00:00
-- url     : https://prove2.me/submissions/e82c3d35-abec-45ab-83a8-2e50150266db

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
public import Theorems.Thm_MatchingLogic_EntryIIIRegression_locConsistent_of_semantic_point
public import Theorems.Thm_MatchingLogic_EntryIIIRegression_unary_has_semantic_point

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIIIRegression
open Set
namespace MatchingLogic.EntryIIIRegression
theorem _root_.solution :
    LocConsistent ({unaryPattern} : Set (Pattern AuditSig Nat)) :=
  locConsistent_of_semantic_point auditModel auditRho false
    unary_has_semantic_point
end MatchingLogic.EntryIIIRegression
