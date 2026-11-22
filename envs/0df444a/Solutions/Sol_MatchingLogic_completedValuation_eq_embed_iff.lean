-- Prove2me | solution 1 for MatchingLogic.completedValuation_eq_embed_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:22.487802+00:00
-- url     : https://prove2.me/submissions/72354ee3-f943-408e-b889-636b8e81d8af

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Completion
public import Theorems.Thm_MatchingLogic_completedEmbed_injective
public import Theorems.Thm_MatchingLogic_mem_completedInterp
public import Theorems.Thm_MatchingLogic_completedModel_interp
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
public import Theorems.Thm_MatchingLogic_GeneratedCarrier_eq_of_var_mem
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_symm
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_trans
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_canonicalModel_interp
public import Theorems.Thm_MatchingLogic_canonicalStep_iff
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_generatedModel_interp
public import Theorems.Thm_MatchingLogic_generatingContext_nil
public import Theorems.Thm_MatchingLogic_generatingStepContext_plug
public import Theorems.Thm_MatchingLogic_mem_canonicalInterp
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
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var
attribute [local simp] MatchingLogic.generatedModel_interp
attribute [local simp] MatchingLogic.generatingContext_nil
attribute [local simp] MatchingLogic.generatingStepContext_plug
attribute [local simp] MatchingLogic.mem_canonicalInterp
attribute [local simp] MatchingLogic.mem_generatedInterp


attribute [local simp] MatchingLogic.mem_completedInterp
attribute [local simp] MatchingLogic.completedModel_interp

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatCompletion
namespace MatchingLogic
theorem _root_.solution (root : CanonicalCarrier S) (x : Nat)
    (world : GeneratedCarrier root) :
    completedValuation root x = completedEmbed root world ↔
      Pattern.var x ∈ world.val.val := by
  classical
  by_cases h : ∃ candidate : GeneratedCarrier root,
      Pattern.var x ∈ candidate.val.val
  · let chosen := Classical.choose h
    have hchosen : Pattern.var x ∈ chosen.val.val := Classical.choose_spec h
    have hvalue : completedValuation root x = completedEmbed root chosen := by
      simp [completedValuation, h, chosen]
    constructor
    · intro heq
      have hchosenWorld : chosen = world :=
        completedEmbed_injective root (hvalue.symm.trans heq)
      simpa [hchosenWorld] using hchosen
    · intro hworld
      have hchosenWorld : chosen = world :=
        GeneratedCarrier.eq_of_var_mem chosen world hchosen hworld
      simp [hvalue, hchosenWorld]
  · constructor
    · intro heq
      have hval := congrArg Subtype.val heq
      simp [completedValuation, h, completedEmbed] at hval
    · intro hworld
      exact False.elim (h ⟨world, hworld⟩)
end MatchingLogic
