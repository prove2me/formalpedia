-- Prove2me | solution 1 for MatchingLogic.necessitation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:00.756226+00:00
-- url     : https://prove2.me/submissions/54b65e2c-ea73-4292-a435-fe9df5653195

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
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


section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
private theorem doubleNegIntro_taut : doubleNegIntro.Taut := by
  intro v
  cases h : v 0 <;> simp [doubleNegIntro, PForm.eval, h]
private theorem implicationTransitivity_taut : implicationTransitivity.Taut := by
  intro v
  cases h₀ : v 0 <;> cases h₁ : v 1 <;> cases h₂ : v 2 <;>
    simp [implicationTransitivity, PForm.eval, h₀, h₁, h₂]
private theorem Provable.imp_trans {Γ : Set (Pattern S Var)} {φ₁ φ₂ φ₃ : Pattern S Var}
    (h₁₂ : Provable Γ (.imp φ₁ φ₂)) (h₂₃ : Provable Γ (.imp φ₂ φ₃)) :
    Provable Γ (.imp φ₁ φ₃) := by
  have ht : Provable Γ
      (.imp (.imp φ₁ φ₂) (.imp (.imp φ₂ φ₃) (.imp φ₁ φ₃))) := by
    exact Provable.taut (p := implicationTransitivity)
      (θ := fun n => if n = 0 then φ₁ else if n = 1 then φ₂ else φ₃)
      implicationTransitivity_taut
  exact Provable.mp h₂₃ (Provable.mp h₁₂ ht)
omit [DecidableEq Var] in
private theorem update_top_eq_dia_args (e : Coord S) (χ : Pattern S Var) :
    Function.update (fun _ : Fin (S.arity e.1) => (Pattern.tp : Pattern S Var)) e.2 χ =
      fun j => if j = e.2 then χ else Pattern.tp := by
  funext j
  by_cases hj : j = e.2
  · subst j
    simp
  · simp [hj]
private theorem necessitation_coord {Γ : Set (Pattern S Var)} {ψ : Pattern S Var}
    (h : Provable Γ ψ) (e : Coord S) : Provable Γ (box e ψ) := by
  have hdnIntro : Provable Γ (.imp ψ (.imp (.imp ψ .bot) .bot)) := by
    exact Provable.taut (p := doubleNegIntro) (θ := fun _ => ψ) doubleNegIntro_taut
  have hdn : Provable Γ (.imp (.imp ψ .bot) .bot) := Provable.mp h hdnIntro
  have hframe : Provable Γ (.imp (dia e (.imp ψ .bot)) (dia e .bot)) := by
    have hframe' := Provable.framing (σ := e.1) (i := e.2)
      (args := fun _ => Pattern.tp) hdn
    simpa only [dia, update_top_eq_dia_args] using hframe'
  have hbot : Provable Γ (.imp (dia e .bot) .bot) := by
    have hbot' := Provable.propBot (Γ := Γ) (σ := e.1) (i := e.2)
      (args := fun _ => Pattern.tp)
    simpa only [dia, update_top_eq_dia_args] using hbot'
  simpa only [box] using Provable.imp_trans hframe hbot
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution {Γ : Set (Pattern S Var)} {ψ : Pattern S Var}
    (h : Provable Γ ψ) (p : List (Coord S)) : Provable Γ (boxes p ψ) := by
  induction p with
  | nil => exact h
  | cons e p ih =>
    simpa only [boxes_cons] using necessitation_coord ih e
end MatchingLogic
