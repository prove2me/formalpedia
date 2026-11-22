-- Prove2me | solution 1 for MatchingLogic.Provable.renameInjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:49.86481+00:00
-- url     : https://prove2.me/submissions/5ab5bf40-cd06-4957-b2b8-48e353a85380

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Theorems.Thm_MatchingLogic_Pattern_rename_id
public import Theorems.Thm_MatchingLogic_Pattern_rename_comp
public import Theorems.Thm_MatchingLogic_Pattern_mem_FV_rename_injective
public import Theorems.Thm_MatchingLogic_Pattern_substVar_rename_injective
public import Theorems.Thm_MatchingLogic_Pattern_captureFree_rename_injective
public import Theorems.Thm_MatchingLogic_Pattern_rename_update
public import Theorems.Thm_MatchingLogic_PForm_subst_rename
public import Theorems.Thm_MatchingLogic_AppCtx_plug_rename_injective
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
namespace Provable
theorem _root_.solution [DecidableEq Var] [DecidableEq Var']
    (f : Var → Var') (hf : Function.Injective f)
    {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (h : Provable Gamma phi) :
    Provable (Pattern.rename f '' Gamma) (phi.rename f) := by
  induction h with
  | hyp hphi => exact .hyp ⟨_, hphi, rfl⟩
  | taut hp =>
      rw [PForm.subst_rename]
      exact .taut hp
  | mp hphi himp ihphi ihimp => exact .mp ihphi ihimp
  | exQuant hfree =>
      simpa [Pattern.rename, Pattern.substVar_rename_injective f hf] using
        (Provable.exQuant (Γ := Pattern.rename f '' Gamma)
          (Pattern.captureFree_rename_injective f hf hfree))
  | exGen himp hfree ih =>
      apply Provable.exGen ih
      intro hmem
      exact hfree ((Pattern.mem_FV_rename_injective f hf _ _).mp hmem)
  | @propBot sigma i args =>
      simpa [Pattern.rename, Pattern.rename_update] using
        (Provable.propBot (Γ := Pattern.rename f '' Gamma)
          (σ := sigma) (i := i) (args := fun j => (args j).rename f))
  | @propOr sigma i args phi1 phi2 =>
      simpa [Pattern.rename, Pattern.or, Pattern.nt, Pattern.rename_update] using
        (Provable.propOr (Γ := Pattern.rename f '' Gamma)
          (σ := sigma) (i := i) (args := fun j => (args j).rename f)
          (φ₁ := phi1.rename f) (φ₂ := phi2.rename f))
  | @propEx sigma i args x phi hfree =>
      have hfree' : ∀ j, j ≠ i → f x ∉ FV ((args j).rename f) := by
        intro j hji hmem
        exact hfree j hji ((Pattern.mem_FV_rename_injective f hf _ _).mp hmem)
      simpa [Pattern.rename, Pattern.rename_update] using
        (Provable.propEx (Γ := Pattern.rename f '' Gamma)
          (σ := sigma) (i := i) (args := fun j => (args j).rename f)
          (x := f x) (φ := phi.rename f) hfree')
  | @framing sigma i args phi1 phi2 himp ih =>
      simpa [Pattern.rename, Pattern.rename_update] using
        (Provable.framing (Γ := Pattern.rename f '' Gamma)
          (σ := sigma) (i := i) (args := fun j => (args j).rename f) ih)
  | @existence x =>
      simpa [Pattern.rename] using
        (Provable.existence (Γ := Pattern.rename f '' Gamma) (x := f x))
  | @singleton x phi C1 C2 =>
      simpa [AppCtx.plug_rename_injective f, Pattern.rename,
        Pattern.and, Pattern.nt] using
        (Provable.singleton (Γ := Pattern.rename f '' Gamma) (x := f x)
          (φ := phi.rename f) (C1.rename f) (C2.rename f))
end Provable
end MatchingLogic
