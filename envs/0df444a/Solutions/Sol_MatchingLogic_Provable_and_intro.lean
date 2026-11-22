-- Prove2me | solution 1 for MatchingLogic.Provable.and_intro
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:19:53.890899+00:00
-- url     : https://prove2.me/submissions/02e6aa9d-55b0-4a4d-828b-53833b0c485c

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
private theorem taut_and_intro :
    PForm.Taut (.imp (.atom 0) (.imp (.atom 1)
      (.imp (.imp (.atom 0) (.imp (.atom 1) .bot)) .bot))) := by
  intro v
  cases h₀ : v 0 <;> cases h₁ : v 1 <;> simp [PForm.eval, h₀, h₁]
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
namespace Provable
theorem _root_.solution {Γ : Set (Pattern S Var)} {φ ψ : Pattern S Var}
    (hφ : Provable Γ φ) (hψ : Provable Γ ψ) :
    Provable Γ (Pattern.and φ ψ) := by
  have ht : Provable Γ (.imp φ (.imp ψ (Pattern.and φ ψ))) := by
    simpa [PForm.subst, Pattern.and, Pattern.nt] using
      (Provable.taut (Γ := Γ) (θ := fun n => if n = 0 then φ else ψ)
        taut_and_intro)
  exact .mp hψ (.mp hφ ht)
end Provable
end MatchingLogic
