-- Prove2me | solution 1 for MatchingLogic.witnessed_freshWitnessed_of_isMCS_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:16.839798+00:00
-- url     : https://prove2.me/submissions/4da25b49-3f95-4f88-a655-2f79ea6de854

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Theorems.Thm_MatchingLogic_witnessCollapseTheory_isMCS
public import Theorems.Thm_MatchingLogic_witnessCollapseTheory_witnessed
public import Theorems.Thm_MatchingLogic_witnessCollapseTheory_not_freshWitnessed

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
noncomputable section
variable {S : Signature}
namespace MatchingLogic
theorem _root_.solution :
    ∃ Gamma : Set (Pattern WitnessCollapseSig Nat),
      IsMCS Gamma ∧ Witnessed Gamma ∧ ¬ FreshWitnessed Gamma := by
  exact ⟨witnessCollapseTheory, witnessCollapseTheory_isMCS,
    witnessCollapseTheory_witnessed, witnessCollapseTheory_not_freshWitnessed⟩
end MatchingLogic
