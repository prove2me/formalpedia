-- Prove2me | solution 1 for MatchingLogic.Pattern.substVar_eq_self_of_not_mem_FV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:19:54.913901+00:00
-- url     : https://prove2.me/submissions/96f30fe3-7fae-41ec-a357-778de0f8c527

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_Sanity
public import Mathlib.Data.Set.BooleanAlgebra
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
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
attribute [local instance] Classical.propDecidable
namespace MatchingLogic
namespace Pattern
theorem _root_.solution {x y : Var} {φ : Pattern S Var}
    (hx : x ∉ FV φ) : substVar x y φ = φ := by
  induction φ with
  | var z =>
      simp only [FV_var, Set.mem_singleton_iff] at hx
      have hzx : z ≠ x := fun h => hx h.symm
      change (if z = x then Pattern.var y else Pattern.var z) = Pattern.var z
      rw [if_neg hzx]
  | bot => rfl
  | app σ f ih =>
      simp only [FV_app, Set.mem_iUnion, not_exists] at hx
      simp only [substVar]
      congr 2
      funext i
      exact ih i (hx i)
  | imp φ ψ ihφ ihψ =>
      simp only [FV_imp, Set.mem_union, not_or] at hx
      simp [substVar, ihφ hx.1, ihψ hx.2]
  | ex z φ ih =>
      by_cases hzx : z = x
      · simp [substVar, hzx]
      · simp only [FV_ex, Set.mem_sdiff, Set.mem_singleton_iff, not_and_or,
          Classical.not_not] at hx
        have hxφ : x ∉ FV φ := by
          intro hmem
          exact hx.resolve_right (fun h => hzx h.symm) hmem
        simp [substVar, hzx, ih hxφ]
end Pattern
end MatchingLogic
