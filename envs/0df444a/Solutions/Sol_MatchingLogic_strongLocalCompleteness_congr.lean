-- Prove2me | solution 1 for MatchingLogic.strongLocalCompleteness_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:33:57.387796+00:00
-- url     : https://prove2.me/submissions/4f2c39c2-3ca1-4713-8e23-fd6aa923a07f

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Theorems.Thm_MatchingLogic_Pattern_rename_id
public import Theorems.Thm_MatchingLogic_Pattern_rename_comp
public import Theorems.Thm_MatchingLogic_rename_conj
public import Theorems.Thm_MatchingLogic_Provable_renameEquiv
public import Theorems.Thm_MatchingLogic_localCons_renameEquiv
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
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


attribute [local simp] MatchingLogic.Pattern.rename_id
attribute [local simp] MatchingLogic.Pattern.rename_comp

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var Var' Var'' : Type}
namespace MatchingLogic
theorem _root_.solution [DecidableEq Var] [DecidableEq Var']
    (e : Var ≃ Var') :
    StrongLocalCompleteness S Var ↔ StrongLocalCompleteness S Var' := by
  constructor
  · intro h
    rw [StrongLocalCompleteness] at h ⊢
    intro Delta phi hlocal
    have hlocal' :
        LocalCons (Pattern.rename e.symm '' Delta) (phi.rename e.symm) :=
      (localCons_renameEquiv e.symm).mp hlocal
    obtain ⟨l, hl, hp⟩ := h _ _ hlocal'
    refine ⟨l.map (Pattern.rename e), ?_, ?_⟩
    · intro delta hdelta
      obtain ⟨q, hql, rfl⟩ := List.mem_map.mp hdelta
      obtain ⟨d, hd, rfl⟩ := hl q hql
      simpa [Pattern.rename_comp] using hd
    · have hp' := hp.renameEquiv e
      simpa [Pattern.rename, rename_conj, Pattern.rename_comp] using hp'
  · intro h
    rw [StrongLocalCompleteness] at h ⊢
    intro Delta phi hlocal
    have hlocal' :
        LocalCons (Pattern.rename e '' Delta) (phi.rename e) :=
      (localCons_renameEquiv e).mp hlocal
    obtain ⟨l, hl, hp⟩ := h _ _ hlocal'
    refine ⟨l.map (Pattern.rename e.symm), ?_, ?_⟩
    · intro delta hdelta
      obtain ⟨q, hql, rfl⟩ := List.mem_map.mp hdelta
      obtain ⟨d, hd, rfl⟩ := hl q hql
      simpa [Pattern.rename_comp] using hd
    · have hp' := hp.renameEquiv e.symm
      simpa [Pattern.rename, rename_conj, Pattern.rename_comp] using hp'
end MatchingLogic
