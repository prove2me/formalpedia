-- Prove2me | solution 1 for MatchingLogic.witnessed_freshWitnessed_of_isMCS_refuted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:30.553718+00:00
-- url     : https://prove2.me/submissions/7fc5bb00-0481-47d7-95e4-61d3cb1df63b

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
    ¬ (∀ {Gamma : Set (Pattern WitnessCollapseSig Nat)},
      IsMCS Gamma → Witnessed Gamma → FreshWitnessed Gamma) := by
  intro hCollapse
  exact witnessCollapseTheory_not_freshWitnessed
    (hCollapse witnessCollapseTheory_isMCS witnessCollapseTheory_witnessed)
end MatchingLogic
