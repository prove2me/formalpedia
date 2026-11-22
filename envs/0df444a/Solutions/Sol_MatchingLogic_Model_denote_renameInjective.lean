-- Prove2me | solution 1 for MatchingLogic.Model.denote_renameInjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:06.786265+00:00
-- url     : https://prove2.me/submissions/a4a00342-6d98-4702-9a2e-1c579858e660

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
namespace MatchingLogic
namespace Model
theorem _root_.solution [DecidableEq Var] [DecidableEq Var']
    (M : Model S) (f : Var → Var') (hf : Function.Injective f)
    (rho : Var' → M.carrier)
    (p : Pattern S Var) :
    M.denote rho (p.rename f) = M.denote (rho ∘ f) p := by
  induction p generalizing rho with
  | var x => rfl
  | bot => rfl
  | app sigma args ih =>
      simp only [Pattern.rename, denote_app]
      congr 2
      funext i
      exact ih i rho
  | imp phi psi ihphi ihpsi =>
      simp only [Pattern.rename, denote_imp]
      rw [ihphi rho, ihpsi rho]
  | ex x phi ih =>
      simp only [Pattern.rename, denote_ex]
      congr 1
      funext a
      rw [ih]
      congr 1
      funext z
      by_cases hzx : z = x
      · subst z
        simp
      · have hfx : f z ≠ f x := fun heq => hzx (hf heq)
        simp [hzx, hfx]
end Model
end MatchingLogic
