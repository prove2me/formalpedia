-- Prove2me | solution 1 for MatchingLogic.witnessCollapseTheory_not_freshWitnessed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:23.791127+00:00
-- url     : https://prove2.me/submissions/b0b1b138-026a-420f-9d17-f3140f8f289b

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_Model_denote_captureAvoidingSubst
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Pattern_IsCaptureAvoidingSubst_denote
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_box
attribute [local simp] MatchingLogic.FV_boxes
attribute [local simp] MatchingLogic.FV_dia
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.Model.reachWord_cons
attribute [local simp] MatchingLogic.Model.reachWord_nil
attribute [local simp] MatchingLogic.boxes_cons
attribute [local simp] MatchingLogic.boxes_nil
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
noncomputable section
variable {S : Signature}
namespace MatchingLogic
theorem _root_.solution :
    ¬ FreshWitnessed witnessCollapseTheory := by
  intro hFresh
  let e : Pattern WitnessCollapseSig Nat := .ex 0 (.var 0)
  have he : e ∈ witnessCollapseTheory := by
    change true ∈ witnessCollapseModel.denote witnessCollapseRho e
    simp [e]
  obtain ⟨y, hyFresh, hyImp⟩ := hFresh he
  have hyNe : y ≠ 0 := by
    simpa [Pattern.allVars] using hyFresh
  change true ∈ witnessCollapseModel.denote witnessCollapseRho
    (.imp e (Pattern.captureAvoidingSubst 0 y (.var 0))) at hyImp
  have hePoint : true ∈ witnessCollapseModel.denote witnessCollapseRho e := he
  have hinstance :
      true ∉ witnessCollapseModel.denote witnessCollapseRho
        (Pattern.captureAvoidingSubst 0 y (.var 0)) := by
    rw [witnessCollapseModel.denote_captureAvoidingSubst]
    simp [witnessCollapseRho, hyNe]
  simp only [denote_imp, Set.mem_union, Set.mem_compl_iff] at hyImp
  exact hyImp.elim (fun hnot => hnot hePoint) (fun hmem => hinstance hmem)
end MatchingLogic
