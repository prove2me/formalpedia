-- Prove2me | solution 1 for MatchingLogic.EntryIIIRegression.open_var_not_empty_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:01.831487+00:00
-- url     : https://prove2.me/submissions/f7bff901-a0e3-4fa3-a441-45143c19f8be

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
public import Theorems.Thm_MatchingLogic_EntryIIIRegression_open_var_not_global_consequence
public import Theorems.Thm_MatchingLogic_soundness


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIIIRegression
open Set
namespace MatchingLogic.EntryIIIRegression
theorem _root_.solution :
    ¬ Provable (∅ : Set (Pattern AuditSig Nat)) (.var 0) := by
  intro hp
  exact open_var_not_global_consequence (soundness _ _ hp)
end MatchingLogic.EntryIIIRegression
