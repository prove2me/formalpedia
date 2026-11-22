-- Prove2me | solution 1 for MatchingLogic.GeneratingPath.plug_mem_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:02.747897+00:00
-- url     : https://prove2.me/submissions/8978a6b7-00c1-4abc-a38f-1b3d01d9a467

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
public import Theorems.Thm_MatchingLogic_AppCtx_plug_comp
public import Theorems.Thm_MatchingLogic_canonicalStep_iff
public import Theorems.Thm_MatchingLogic_mem_generatedInterp
public import Theorems.Thm_MatchingLogic_generatedModel_interp
public import Theorems.Thm_MatchingLogic_generatingStepContext_plug
public import Theorems.Thm_MatchingLogic_generatingContext_nil
public import Theorems.Thm_MatchingLogic_generatingContext_append
public import Theorems.Thm_MatchingLogic_CanonicalCarrier_top_mem
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
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_mem_canonicalInterp
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
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var
attribute [local simp] MatchingLogic.mem_canonicalInterp


attribute [local simp] MatchingLogic.AppCtx.plug_comp
attribute [local simp] MatchingLogic.canonicalStep_iff
attribute [local simp] MatchingLogic.mem_generatedInterp
attribute [local simp] MatchingLogic.generatedModel_interp
attribute [local simp] MatchingLogic.generatingStepContext_plug
attribute [local simp] MatchingLogic.generatingContext_nil

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatGenerated
namespace MatchingLogic
namespace GeneratingPath
theorem _root_.solution {root world : CanonicalCarrier S}
    {path : List (Coord S)} (hpath : GeneratingPath root world path)
    {p : Pattern S Nat} (hp : p ∈ (world : Set (Pattern S Nat))) :
    (generatingContext path).plug p ∈ (root : Set (Pattern S Nat)) := by
  induction hpath generalizing p with
  | root => simpa [generatingContext, AppCtx.plug] using hp
  | @tail parent path sigma components i hpath hinterp ih =>
      let args : Fin (S.arity sigma) → Pattern S Nat :=
        Function.update (fun _ => Pattern.tp) i p
      have hargs : ∀ j, args j ∈ (components j : Set (Pattern S Nat)) := by
        intro j
        by_cases hji : j = i
        · subst j
          simpa [args] using hp
        · rw [show args j = Pattern.tp by simp [args, hji]]
          exact CanonicalCarrier.top_mem (components j)
      have happ : Pattern.app sigma args ∈
          (parent : Set (Pattern S Nat)) :=
        (mem_canonicalInterp.mp hinterp) args hargs
      have hout := ih happ
      rw [generatingContext_append, AppCtx.plug_comp,
        generatingStepContext_plug]
      exact hout
end GeneratingPath
end MatchingLogic
