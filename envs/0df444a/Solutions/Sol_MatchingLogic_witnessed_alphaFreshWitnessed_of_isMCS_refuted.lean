-- Prove2me | solution 1 for MatchingLogic.witnessed_alphaFreshWitnessed_of_isMCS_refuted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:47:15.807398+00:00
-- url     : https://prove2.me/submissions/276fd301-4b83-4d89-8f20-913e2f7e9422

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Mathlib.Tactic.FinCases
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_AlphaFreshWitnessed
public import Theorems.Thm_MatchingLogic_alphaWitnessTheory_isMCS
public import Theorems.Thm_MatchingLogic_alphaWitnessTheory_witnessed
public import Theorems.Thm_MatchingLogic_alphaWitnessTheory_not_alphaFreshWitnessed

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
noncomputable section
namespace MatchingLogic
theorem _root_.solution :
    ¬ (∀ {Gamma : Set (Pattern AlphaWitnessSig Nat)},
      IsMCS Gamma → Witnessed Gamma → AlphaFreshWitnessed Gamma) := by
  intro hCollapse
  exact alphaWitnessTheory_not_alphaFreshWitnessed
    (hCollapse alphaWitnessTheory_isMCS alphaWitnessTheory_witnessed)
end MatchingLogic
