-- Prove2me | solution 1 for MatchingLogic.Provable.witnessPush
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:04.923232+00:00
-- url     : https://prove2.me/submissions/e59e1813-6c62-4e44-ad91-f984726ee971

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Theorems.Thm_MatchingLogic_Pattern_captureAvoidingSubst_not_mem_FV_of_ne
public import Theorems.Thm_MatchingLogic_Provable_witnessPushArg
public import Theorems.Thm_MatchingLogic_Provable_app_exists_list
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
public import Theorems.Thm_MatchingLogic_Provable_imp_trans
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
namespace Provable
theorem _root_.solution {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat) (phi : Pattern S Nat)
    (x : Nat) (y : Fin (S.arity sigma) -> Nat)
    (hyinj : Function.Injective y)
    (hyphi : forall i, y i ∉ FV phi)
    (hyPhi : forall i j, y i ∉ FV (Phi j)) :
    Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma Phi)
        (Pattern.exList (List.ofFn y)
          (.app sigma (fun i => Pattern.and (Phi i)
            (.imp (.ex x phi)
              (Pattern.captureAvoidingSubst x (y i) phi)))))) := by
  let body : Fin (S.arity sigma) -> Pattern S Nat := fun i =>
    Pattern.and (Phi i)
      (.imp (.ex x phi) (Pattern.captureAvoidingSubst x (y i) phi))
  have hargs : forall i, Provable (∅ : Set (Pattern S Nat))
      (.imp (Phi i) (.ex (y i) (body i))) := by
    intro i
    simpa [body] using
      (Provable.witnessPushArg (Gamma := (∅ : Set (Pattern S Nat)))
        (x := x) (y := y i) (phi := phi) (Phi := Phi i)
        (hyphi i) (hyPhi i i))
  have happ : Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma Phi) (.app sigma (fun i => .ex (y i) (body i)))) :=
    Provable.app_mono hargs
  have hfresh : forall i j, i ≠ j -> y i ∉ FV (body j) := by
    intro i j hij
    have hyne : y i ≠ y j := hyinj.ne hij
    have hca : y i ∉ FV (Pattern.captureAvoidingSubst x (y j) phi) :=
      Pattern.captureAvoidingSubst_not_mem_FV_of_ne hyne (hyphi i)
    simp [body, Pattern.and, Pattern.nt, hyPhi i j, hyphi i, hca]
  exact happ.imp_trans (by
    simpa [body] using
      (Provable.app_exists_list (Gamma := (∅ : Set (Pattern S Nat)))
        (sigma := sigma) y body hfresh))
end Provable
end MatchingLogic
