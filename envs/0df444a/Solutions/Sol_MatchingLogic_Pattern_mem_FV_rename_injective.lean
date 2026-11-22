-- Prove2me | solution 1 for MatchingLogic.Pattern.mem_FV_rename_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:06.110283+00:00
-- url     : https://prove2.me/submissions/17128175-5299-47b1-a428-6b4c81b1deeb

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Theorems.Thm_MatchingLogic_Pattern_rename_id
public import Theorems.Thm_MatchingLogic_Pattern_rename_comp
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
open MatchingLogic.Pattern
namespace MatchingLogic.Pattern
theorem _root_.solution
    (f : Var → Var') (hf : Function.Injective f) (p : Pattern S Var) (x : Var) :
    f x ∈ FV (p.rename f) ↔ x ∈ FV p := by
  classical
  induction p with
  | var y => simp [rename, hf.eq_iff]
  | bot => simp [rename]
  | app sigma args ih =>
      simp only [rename, FV_app, Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (ih i).mp hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (ih i).mpr hi⟩
  | imp phi psi ihphi ihpsi => simp [rename, ihphi, ihpsi]
  | ex y phi ih =>
      simp only [rename, FV_ex, Set.mem_sdiff, Set.mem_singleton_iff, ih]
      exact and_congr Iff.rfl (not_congr hf.eq_iff)
end MatchingLogic.Pattern
