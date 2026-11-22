-- Prove2me | solution 1 for MatchingLogic.Model.denote_substVar_of_captureFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:00.950326+00:00
-- url     : https://prove2.me/submissions/5f60c0b9-dcf0-404c-a2d7-608621b0dede

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_Sanity
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Theorems.Thm_MatchingLogic_Pattern_substVar_eq_self_of_not_mem_FV
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
public import Theorems.Thm_MatchingLogic_denote_congr
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
attribute [local instance] Classical.propDecidable
namespace MatchingLogic
namespace Model
theorem _root_.solution (M : Model S) (ρ : Var → M.carrier)
    {x y : Var} {φ : Pattern S Var} (hcf : CaptureFree x y φ) :
    M.denote ρ (substVar x y φ) =
      M.denote (Function.update ρ x (ρ y)) φ := by
  induction φ generalizing ρ with
  | var z =>
      by_cases hzx : z = x
      · subst z
        simp [substVar]
      · simp [substVar, hzx]
  | bot => simp [substVar]
  | app σ f ih =>
      simp only [substVar, denote_app]
      congr 2
      funext i
      exact ih i ρ (hcf i)
  | imp φ ψ ihφ ihψ =>
      exact congrArg₂ (fun A B : Set M.carrier => Aᶜ ∪ B)
        (ihφ ρ hcf.1) (ihψ ρ hcf.2)
  | ex z φ ih =>
      rcases hcf with hzx | hxfree | ⟨hzy, hrec⟩
      · subst z
        simp [substVar]
      · by_cases hzx : z = x
        · subst z
          simp [substVar]
        · rw [substVar]
          simp only [if_neg hzx, denote_ex]
          congr 1
          funext a
          rw [Pattern.substVar_eq_self_of_not_mem_FV hxfree]
          apply denote_congr M φ
          intro q hq
          have hqx : q ≠ x := fun h => hxfree (h ▸ hq)
          by_cases hqz : q = z
          · subst q
            simp
          · simp [hqz, hqx]
      · by_cases hzx : z = x
        · subst z
          simp [substVar]
        · rw [substVar]
          simp only [if_neg hzx, denote_ex]
          congr 1
          funext a
          rw [ih (Function.update ρ z a) hrec]
          congr 1
          funext q
          by_cases hqz : q = z
          · subst q
            simp [Function.update_apply, hzx]
          · by_cases hqx : q = x
            · subst q
              simp [Ne.symm hzy, hqz]
            · simp [Function.update_apply, hqz, hqx]
end Model
end MatchingLogic
