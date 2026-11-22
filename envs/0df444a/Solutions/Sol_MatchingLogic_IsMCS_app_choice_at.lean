-- Prove2me | solution 1 for MatchingLogic.IsMCS.app_choice_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:23.584811+00:00
-- url     : https://prove2.me/submissions/4c7ace4c-0610-4c24-a833-663952358986

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalChoice
public import Theorems.Thm_MatchingLogic_Provable_and_decide
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_IsMCS_mem_of_provable_imp
public import Theorems.Thm_MatchingLogic_IsMCS_or_mem_iff
public import Theorems.Thm_MatchingLogic_LocProvable_mp
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
variable {S : Signature}
namespace MatchingLogic
namespace IsMCS
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) {sigma : S.Sym}
    (args : Fin (S.arity sigma) -> Pattern S Nat)
    (i : Fin (S.arity sigma)) (psi : Pattern S Nat)
    (happ : Pattern.app sigma args ∈ Gamma) :
    ∃ b : Bool,
      Pattern.app sigma
        (Function.update args i
          (Pattern.and (args i) (if b then psi else Pattern.nt psi))) ∈ Gamma := by
  let pos : Pattern S Nat := Pattern.and (args i) psi
  let neg : Pattern S Nat := Pattern.and (args i) (Pattern.nt psi)
  have hframe0 := Provable.framing (Γ := (∅ : Set (Pattern S Nat)))
    (σ := sigma) (i := i) (args := args)
    (Provable.and_decide (Gamma := (∅ : Set (Pattern S Nat))) (args i) psi)
  have hframe : Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma args)
        (.app sigma (Function.update args i (Pattern.or pos neg)))) := by
    simpa [pos, neg] using hframe0
  have hdisjArg : Pattern.app sigma
      (Function.update args i (Pattern.or pos neg)) ∈ Gamma :=
    hM.mem_of_provable_imp happ hframe
  have hdisjApp : Pattern.or
      (.app sigma (Function.update args i pos))
      (.app sigma (Function.update args i neg)) ∈ Gamma :=
    hM.mem_of_provable_imp hdisjArg
      (Provable.propOr (Γ := (∅ : Set (Pattern S Nat)))
        (σ := sigma) (i := i) (args := args) (φ₁ := pos) (φ₂ := neg))
  rcases hM.or_mem_iff.mp hdisjApp with hpos | hneg
  · exact ⟨true, by simpa [pos] using hpos⟩
  · exact ⟨false, by simpa [neg] using hneg⟩
end IsMCS
end MatchingLogic
