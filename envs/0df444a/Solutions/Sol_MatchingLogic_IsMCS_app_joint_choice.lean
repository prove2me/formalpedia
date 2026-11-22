-- Prove2me | solution 1 for MatchingLogic.IsMCS.app_joint_choice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:33.02404+00:00
-- url     : https://prove2.me/submissions/93382702-08be-4ef4-abb5-adde09d92d84

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalChoice
public import Theorems.Thm_MatchingLogic_IsMCS_app_choice_at
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
variable {S : Signature}
private theorem IsMCS.app_joint_choice_aux {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat)
    (psi : Pattern S Nat) (happ : Pattern.app sigma Phi ∈ Gamma)
    (selected : Finset (Fin (S.arity sigma))) :
    ∃ choose : Fin (S.arity sigma) -> Bool,
      Pattern.app sigma (Pattern.choiceArgs selected choose Phi psi) ∈ Gamma := by
  induction selected using Finset.induction_on with
  | empty =>
      refine ⟨fun _ => false, ?_⟩
      have heq : Pattern.choiceArgs ∅ (fun _ => false) Phi psi = Phi := by
        funext i
        simp [Pattern.choiceArgs]
      simpa [heq] using happ
  | @insert i selected hi ih =>
      rcases ih with ⟨choose, hchosen⟩
      rcases hM.app_choice_at (Pattern.choiceArgs selected choose Phi psi) i psi
          hchosen with ⟨b, hb⟩
      let choose' := Function.update choose i b
      refine ⟨choose', ?_⟩
      have heq :
          Function.update (Pattern.choiceArgs selected choose Phi psi) i
              (Pattern.and (Pattern.choiceArgs selected choose Phi psi i)
                (if b then psi else Pattern.nt psi)) =
            Pattern.choiceArgs (insert i selected) choose' Phi psi := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [Pattern.choiceArgs, hi, choose']
        · simp [Pattern.choiceArgs, hji, choose']
      simpa only [heq] using hb
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
namespace IsMCS
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    (hM : IsMCS Gamma) {sigma : S.Sym}
    (Phi : Fin (S.arity sigma) -> Pattern S Nat)
    (psi : Pattern S Nat) (happ : Pattern.app sigma Phi ∈ Gamma) :
    ∃ choose : Fin (S.arity sigma) -> Bool,
      Pattern.app sigma (fun i =>
        Pattern.and (Phi i) (if choose i then psi else Pattern.nt psi)) ∈ Gamma := by
  rcases hM.app_joint_choice_aux Phi psi happ Finset.univ with ⟨choose, hchoose⟩
  refine ⟨choose, ?_⟩
  have heq : Pattern.choiceArgs Finset.univ choose Phi psi = fun i =>
      Pattern.and (Phi i) (if choose i then psi else Pattern.nt psi) := by
    funext i
    simp [Pattern.choiceArgs]
  simpa [heq] using hchoose
end IsMCS
end MatchingLogic
