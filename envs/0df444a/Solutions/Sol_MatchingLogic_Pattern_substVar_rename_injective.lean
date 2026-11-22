-- Prove2me | solution 1 for MatchingLogic.Pattern.substVar_rename_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:07.422899+00:00
-- url     : https://prove2.me/submissions/e8909a67-a79b-465a-92c3-54a6c93d4210

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
theorem _root_.solution [DecidableEq Var] [DecidableEq Var']
    (f : Var → Var') (hf : Function.Injective f) (x y : Var) (p : Pattern S Var) :
    (substVar x y p).rename f = substVar (f x) (f y) (p.rename f) := by
  induction p with
  | var z =>
      by_cases hzx : z = x
      · simp [substVar, Pattern.rename, hzx]
      · simp [substVar, Pattern.rename, hzx, hf.eq_iff]
  | app sigma args ih =>
      simp only [substVar, rename]
      congr
      funext i
      exact ih i
  | imp phi psi ihphi ihpsi => simp [substVar, rename, ihphi, ihpsi]
  | bot => rfl
  | ex z phi ih =>
      by_cases hzx : z = x
      · simp [substVar, Pattern.rename, hzx]
      · simp [substVar, Pattern.rename, hzx, hf.eq_iff, ih]
end MatchingLogic.Pattern
