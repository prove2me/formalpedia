-- Prove2me | solution 1 for MatchingLogic.finiteLocalModelExistence_of_canonicalExistence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:16.901933+00:00
-- url     : https://prove2.me/submissions/88468fc8-48c0-44a1-9af3-a3b199b08532

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalExistence
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Truth
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_ModelExistence
public import Theorems.Thm_MatchingLogic_AppCtx_plug_comp
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_coe_mk
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_canonicalModel_interp
public import Theorems.Thm_MatchingLogic_canonicalStep_iff
public import Theorems.Thm_MatchingLogic_completedModel_interp
public import Theorems.Thm_MatchingLogic_completed_truth
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_finite_locConsistent_extend_freshWitnessed_isMCS
public import Theorems.Thm_MatchingLogic_generatedModel_interp
public import Theorems.Thm_MatchingLogic_generatingContext_nil
public import Theorems.Thm_MatchingLogic_generatingStepContext_plug
public import Theorems.Thm_MatchingLogic_mem_canonicalInterp
public import Theorems.Thm_MatchingLogic_mem_completedInterp
public import Theorems.Thm_MatchingLogic_mem_generatedInterp
attribute [local simp] MatchingLogic.AppCtx.plug_comp
attribute [local simp] MatchingLogic.CanonicalCarrier.coe_mk
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
attribute [local simp] MatchingLogic.canonicalModel_interp
attribute [local simp] MatchingLogic.canonicalStep_iff
attribute [local simp] MatchingLogic.completedModel_interp
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var
attribute [local simp] MatchingLogic.generatedModel_interp
attribute [local simp] MatchingLogic.generatingContext_nil
attribute [local simp] MatchingLogic.generatingStepContext_plug
attribute [local simp] MatchingLogic.mem_canonicalInterp
attribute [local simp] MatchingLogic.mem_completedInterp
attribute [local simp] MatchingLogic.mem_generatedInterp



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatModelExistence
namespace MatchingLogic
theorem _root_.solution
    [Countable (Pattern S Nat)] (hExist : CanonicalExistenceProperty S) :
    FiniteLocalModelExistence S Nat := by
  intro l hconsistent
  obtain ⟨Delta, hbase, hM, hW⟩ :=
    finite_locConsistent_extend_freshWitnessed_isMCS l hconsistent
  let root : CanonicalCarrier S := ⟨Delta, hM, hW⟩
  let world : GeneratedCarrier root := generatedRoot root
  refine ⟨completedModel root, completedValuation root,
    completedEmbed root world, ?_⟩
  simp only [Model.denoteSet, Set.mem_iInter]
  intro delta hdelta
  apply (completed_truth hExist root world delta).mp
  exact hbase hdelta
end MatchingLogic
