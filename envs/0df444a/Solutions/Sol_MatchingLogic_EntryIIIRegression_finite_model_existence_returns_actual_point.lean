-- Prove2me | solution 1 for MatchingLogic.EntryIIIRegression.finite_model_existence_returns_actual_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:46:31.292797+00:00
-- url     : https://prove2.me/submissions/44a2576a-a952-4a20-abda-19530c9f3efa

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
public import Theorems.Thm_MatchingLogic_EntryIIIRegression_top_list_locConsistent
public import Theorems.Thm_MatchingLogic_finiteLocalModelExistence


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIIIRegression
open Set
namespace MatchingLogic.EntryIIIRegression
theorem _root_.solution :
    ∃ (M : Model AuditSig) (rho : Nat → M.carrier) (u : M.carrier),
      u ∈ M.denoteSet rho
        {delta : Pattern AuditSig Nat |
          delta ∈ [(Pattern.tp : Pattern AuditSig Nat)]} :=
  finiteLocalModelExistence [(Pattern.tp : Pattern AuditSig Nat)]
    top_list_locConsistent
end MatchingLogic.EntryIIIRegression
