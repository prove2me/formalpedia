-- Prove2me | solution 1 for MatchingLogic.Provable.liftSignature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:15.726505+00:00
-- url     : https://prove2.me/submissions/8e3c7025-c823-4a83-b187-2a3b5079feed

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SymbolSupport
public import Mathlib.Logic.Equiv.List
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureRestriction
public import Theorems.Thm_MatchingLogic_Pattern_liftSignature_substVar
public import Theorems.Thm_MatchingLogic_Pattern_FV_liftSignature
public import Theorems.Thm_MatchingLogic_Pattern_captureFree_liftSignature
public import Theorems.Thm_MatchingLogic_Pattern_liftSignature_app_update
public import Theorems.Thm_MatchingLogic_PForm_subst_liftSignature
public import Theorems.Thm_MatchingLogic_AppCtx_plug_liftSignature
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



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
namespace Provable
theorem _root_.solution [DecidableEq S.Sym] (F : Finset S.Sym)
    {Gamma : Set (Pattern (S.restrict F) Var)} {phi : Pattern (S.restrict F) Var}
    (h : Provable Gamma phi) :
    Provable (Pattern.liftSignature F '' Gamma) (phi.liftSignature F) := by
  induction h with
  | hyp hphi => exact .hyp ⟨_, hphi, rfl⟩
  | taut hp =>
      rw [PForm.subst_liftSignature]
      exact .taut hp
  | mp hphi himp ihphi ihimp => exact .mp ihphi ihimp
  | exQuant hfree =>
      simpa [Pattern.liftSignature, Pattern.liftSignature_substVar] using
        (Provable.exQuant (S := S) (Var := Var) (Γ := Pattern.liftSignature F '' Gamma)
          (Pattern.captureFree_liftSignature F hfree))
  | exGen himp hfree ih =>
      apply Provable.exGen ih
      intro hmem
      apply hfree
      simpa [Pattern.FV_liftSignature] using hmem
  | @propBot sigma i args =>
      have h := Provable.propBot (S := S) (Var := Var)
        (Γ := Pattern.liftSignature F '' Gamma)
        (σ := sigma.1) (i := i) (args := fun j => (args j).liftSignature F)
      change Provable (Pattern.liftSignature F '' Gamma)
        (.imp ((Pattern.app sigma (Function.update args i .bot)).liftSignature F) .bot)
      rw [Pattern.liftSignature_app_update]
      exact h
  | @propOr sigma i args phi₁ phi₂ =>
      have h := Provable.propOr (S := S) (Var := Var)
        (Γ := Pattern.liftSignature F '' Gamma)
        (σ := sigma.1) (i := i) (args := fun j => (args j).liftSignature F)
        (φ₁ := phi₁.liftSignature F) (φ₂ := phi₂.liftSignature F)
      change Provable (Pattern.liftSignature F '' Gamma)
        (.imp ((Pattern.app sigma (Function.update args i (Pattern.or phi₁ phi₂))).liftSignature F)
          (Pattern.or ((Pattern.app sigma (Function.update args i phi₁)).liftSignature F)
            ((Pattern.app sigma (Function.update args i phi₂)).liftSignature F)))
      rw [Pattern.liftSignature_app_update, Pattern.liftSignature_app_update,
        Pattern.liftSignature_app_update]
      rw [show (Pattern.or phi₁ phi₂).liftSignature F =
        Pattern.or (phi₁.liftSignature F) (phi₂.liftSignature F) by rfl]
      exact h
  | @propEx sigma i args x phi hfree =>
      have hfree' : ∀ j, j ≠ i → x ∉ FV ((args j).liftSignature F) := by
        intro j hji hmem
        apply hfree j hji
        simpa [Pattern.FV_liftSignature] using hmem
      have h := Provable.propEx (S := S) (Var := Var)
        (Γ := Pattern.liftSignature F '' Gamma)
        (σ := sigma.1) (i := i) (args := fun j => (args j).liftSignature F)
        (x := x) (φ := phi.liftSignature F) hfree'
      change Provable (Pattern.liftSignature F '' Gamma)
        (.imp ((Pattern.app sigma (Function.update args i (.ex x phi))).liftSignature F)
          (.ex x ((Pattern.app sigma (Function.update args i phi)).liftSignature F)))
      rw [Pattern.liftSignature_app_update, Pattern.liftSignature_app_update]
      exact h
  | @framing sigma i args phi₁ phi₂ himp ih =>
      have h := Provable.framing (S := S) (Var := Var)
        (Γ := Pattern.liftSignature F '' Gamma)
        (σ := sigma.1) (i := i) (args := fun j => (args j).liftSignature F) ih
      change Provable (Pattern.liftSignature F '' Gamma)
        (.imp ((Pattern.app sigma (Function.update args i phi₁)).liftSignature F)
          ((Pattern.app sigma (Function.update args i phi₂)).liftSignature F))
      rw [Pattern.liftSignature_app_update, Pattern.liftSignature_app_update]
      exact h
  | @existence x =>
      simpa [Pattern.liftSignature] using
        (Provable.existence (S := S) (Var := Var)
          (Γ := Pattern.liftSignature F '' Gamma) (x := x))
  | @singleton x phi C₁ C₂ =>
      simpa [AppCtx.plug_liftSignature, Pattern.liftSignature, Pattern.and, Pattern.nt] using
        (Provable.singleton (S := S) (Var := Var)
          (Γ := Pattern.liftSignature F '' Gamma) (x := x)
          (φ := phi.liftSignature F) (C₁.liftSignature F) (C₂.liftSignature F))
end Provable
end MatchingLogic
