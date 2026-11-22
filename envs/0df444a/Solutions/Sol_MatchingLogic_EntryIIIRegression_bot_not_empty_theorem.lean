-- Prove2me | solution 1 for MatchingLogic.EntryIIIRegression.bot_not_empty_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:57.307064+00:00
-- url     : https://prove2.me/submissions/a5af47e6-2a5a-4a5c-92fa-c89ab98a272e

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
public import Theorems.Thm_MatchingLogic_EntryIIIRegression_bot_not_global_consequence
public import Theorems.Thm_MatchingLogic_soundness


set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic MatchingLogic.EntryIIIRegression
open Set
namespace MatchingLogic.EntryIIIRegression
theorem _root_.solution :
    ¬ Provable (∅ : Set (Pattern AuditSig Nat)) .bot := by
  intro hp
  exact bot_not_global_consequence (soundness _ _ hp)
end MatchingLogic.EntryIIIRegression
