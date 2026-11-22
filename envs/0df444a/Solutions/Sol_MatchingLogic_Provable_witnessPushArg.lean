-- Prove2me | solution 1 for MatchingLogic.Provable.witnessPushArg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:26.892406+00:00
-- url     : https://prove2.me/submissions/a571945a-1a5b-45c8-9fe6-b06e811d49f4

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Theorems.Thm_MatchingLogic_Provable_exists_captureAvoidingSubst
public import Theorems.Thm_MatchingLogic_Provable_imp_exists_to_exists_imp
public import Theorems.Thm_MatchingLogic_Provable_and_exists
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
namespace Pattern
end Pattern
private theorem taut_and_with :
    PForm.Taut
      (.imp (.atom 0)
        (.imp (.atom 1)
          (.imp (.imp (.atom 1) (.imp (.atom 0) .bot)) .bot))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]
namespace Pattern
end Pattern
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
    {x y : Nat} {phi Phi : Pattern S Nat}
    (hyphi : y ∉ FV phi) (hyPhi : y ∉ FV Phi) :
    Provable Gamma (.imp Phi
      (.ex y (Pattern.and Phi
        (.imp (.ex x phi) (Pattern.captureAvoidingSubst x y phi))))) := by
  let e : Pattern S Nat := .ex x phi
  let q : Pattern S Nat := Pattern.captureAvoidingSubst x y phi
  let r : Pattern S Nat := .ex y (.imp e q)
  have heq : Provable Gamma (.imp e (.ex y q)) := by
    simpa [e, q] using
      (Provable.exists_captureAvoidingSubst (Gamma := Gamma) hyphi)
  have her : Provable Gamma (.imp (.imp e (.ex y q)) r) := by
    exact Provable.imp_exists_to_exists_imp
  have hr : Provable Gamma r := .mp heq her
  have hPhi : Provable Gamma (.imp Phi (Pattern.and Phi r)) := by
    have ht : Provable Gamma
        (.imp r (.imp Phi (Pattern.and Phi r))) := by
      simpa [PForm.subst, Pattern.and, Pattern.nt] using
        (Provable.taut (Γ := Gamma)
          (θ := fun n => if n = 0 then r else Phi) taut_and_with)
    exact .mp hr ht
  exact hPhi.imp_trans (by
    simpa [r, e, q] using
      (Provable.and_exists (Gamma := Gamma) (y := y)
        (p := Phi) (q := .imp e q) hyPhi))
end Provable
end MatchingLogic
