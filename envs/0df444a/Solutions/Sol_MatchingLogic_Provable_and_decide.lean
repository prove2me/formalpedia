-- Prove2me | solution 1 for MatchingLogic.Provable.and_decide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:24.892801+00:00
-- url     : https://prove2.me/submissions/313e3890-5956-4f71-9fd3-9c594e7c8f78

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalChoice
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Provable_imp_refl
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


section
@[expose] public section
namespace MatchingLogic
variable {S : Signature}
private theorem taut_and_intro :
    PForm.Taut (.imp (.atom 1) (.imp (.atom 0) (pfAnd (.atom 0) (.atom 1)))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;>
    simp [pfAnd, pfNot, PForm.eval, h0, h1]
private theorem taut_and_or_distrib :
    PForm.Taut
      (.imp (pfAnd (.atom 0) (pfOr (.atom 1) (pfNot (.atom 1))))
        (pfOr (pfAnd (.atom 0) (.atom 1))
          (pfAnd (.atom 0) (pfNot (.atom 1))))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;>
    simp [pfAnd, pfOr, pfNot, PForm.eval, h0, h1]
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
namespace MatchingLogic
namespace Provable
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    (Phi psi : Pattern S Nat) :
    Provable Gamma (.imp Phi
      (Pattern.or (Pattern.and Phi psi) (Pattern.and Phi (Pattern.nt psi)))) := by
  let em : Pattern S Nat := Pattern.or psi (Pattern.nt psi)
  have hem : Provable Gamma em := by
    simpa [em, Pattern.or] using
      (Provable.imp_refl Gamma (Pattern.nt psi))
  have hkeep : Provable Gamma (.imp em (.imp Phi (Pattern.and Phi em))) := by
    simpa [PForm.subst, pfAnd, pfNot, Pattern.and, Pattern.nt] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then Phi else em) taut_and_intro)
  have hconj : Provable Gamma (.imp Phi (Pattern.and Phi em)) := .mp hem hkeep
  have hdist : Provable Gamma
      (.imp (Pattern.and Phi em)
        (Pattern.or (Pattern.and Phi psi) (Pattern.and Phi (Pattern.nt psi)))) := by
    simpa [PForm.subst, pfAnd, pfOr, pfNot, Pattern.and, Pattern.or,
      Pattern.nt, em] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then Phi else psi) taut_and_or_distrib)
  exact hconj.imp_trans hdist
end Provable
end MatchingLogic
