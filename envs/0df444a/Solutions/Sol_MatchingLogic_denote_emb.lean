-- Prove2me | solution 1 for MatchingLogic.denote_emb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:14.638831+00:00
-- url     : https://prove2.me/submissions/8f8f7197-121c-45dd-ad49-0329e52cc49b

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Definedness
public import Theorems.Thm_MatchingLogic_AgreeOn_update
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
theorem _root_.solution (M : Model S) (ρ : Var → M.carrier) (φ : Pattern S Var) :
    (expand M).denote ρ (emb φ) = M.denote ρ φ := by
  unfold expand
  induction φ generalizing ρ with
  | var x => rfl
  | bot => rfl
  | app σ f ih =>
      simp only [emb, denote_app]
      ext u
      constructor
      · rintro ⟨a, ha, hu⟩
        refine ⟨a, ?_, hu⟩
        intro i
        have hi := Set.ext_iff.mp (ih i ρ) (a i)
        exact hi.mp (by simpa only using ha i)
      · rintro ⟨a, ha, hu⟩
        refine ⟨a, ?_, hu⟩
        intro i
        have hi := Set.ext_iff.mp (ih i ρ) (a i)
        exact hi.mpr (by simpa only using ha i)
  | imp φ ψ ihφ ihψ =>
      simp only [emb, denote_imp]
      rw [ihφ, ihψ]
  | ex x φ ih =>
      simp only [emb, denote_ex]
      ext u
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, (ih (Function.update ρ x a)) ▸ ha⟩
      · rintro ⟨a, ha⟩
        exact ⟨a, (ih (Function.update ρ x a)).symm ▸ ha⟩
end MatchingLogic
