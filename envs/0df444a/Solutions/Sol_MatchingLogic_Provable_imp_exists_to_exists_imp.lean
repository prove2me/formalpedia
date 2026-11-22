-- Prove2me | solution 1 for MatchingLogic.Provable.imp_exists_to_exists_imp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:30.224406+00:00
-- url     : https://prove2.me/submissions/6eb96cb5-2c4b-47c2-9202-db85918d37cc

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
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
public import Theorems.Thm_MatchingLogic_Pattern_IsCaptureAvoidingSubst_exQuant
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
private theorem taut_imp_of :
    PForm.Taut (.imp (.atom 0) (.imp (.atom 1) (.atom 0))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]
private theorem taut_false_imp :
    PForm.Taut
      (.imp (.imp (.atom 0) .bot) (.imp (.atom 0) (.atom 1))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]
private theorem taut_choice :
    PForm.Taut
      (.imp (.imp (.atom 1) (.atom 2))
        (.imp (.imp (.imp (.atom 0) .bot) (.atom 2))
          (.imp (.imp (.atom 0) (.atom 1)) (.atom 2)))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    simp [PForm.eval, h0, h1, h2]
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
    {y : Nat} {a q : Pattern S Nat} :
    Provable Gamma (.imp (.imp a (.ex y q)) (.ex y (.imp a q))) := by
  let e : Pattern S Nat := .ex y q
  let r : Pattern S Nat := .ex y (.imp a q)
  have hq : Provable Gamma (.imp q (.imp a q)) := by
    simpa [PForm.subst] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then q else a) taut_imp_of)
  have her : Provable Gamma (.imp e r) := by
    simpa [e, r] using Provable.ex_mono hq
  have hna : Provable Gamma (.imp (Pattern.nt a) (.imp a q)) := by
    simpa [PForm.subst, Pattern.nt] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then a else q) taut_false_imp)
  have hir : Provable Gamma (.imp (.imp a q) r) := by
    simpa [r, Pattern.substVar_self] using
      (Provable.exQuant (Γ := Gamma)
        (Pattern.captureFree_self y (.imp a q)))
  have hnar : Provable Gamma (.imp (Pattern.nt a) r) := hna.imp_trans hir
  have ht : Provable Gamma
      (.imp (.imp e r)
        (.imp (.imp (Pattern.nt a) r) (.imp (.imp a e) r))) := by
    simpa [PForm.subst, Pattern.nt] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then a else if n = 1 then e else r)
        taut_choice)
  exact .mp hnar (.mp her ht)
end Provable
end MatchingLogic
