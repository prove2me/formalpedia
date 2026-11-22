-- Prove2me | solution 1 for MatchingLogic.Provable.and_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:39.30785+00:00
-- url     : https://prove2.me/submissions/5321fcfe-6272-4801-8c5e-c6919a0559c8

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
public import Theorems.Thm_MatchingLogic_Provable_and_elim_right
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
private theorem taut_right_conj :
    PForm.Taut (.imp (.atom 0)
      (.imp
        (.imp (.imp (.atom 1) (.imp (.atom 2) .bot)) .bot)
        (.imp (.imp (.atom 1) (.imp (.atom 0) .bot)) .bot))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    simp [PForm.eval, h0, h1, h2]
private theorem taut_nested_trans :
    PForm.Taut
      (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2)))
        (.imp (.imp (.atom 2) (.atom 3))
          (.imp (.atom 0) (.imp (.atom 1) (.atom 3))))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    cases h3 : v 3 <;> simp [PForm.eval, h0, h1, h2, h3]
private theorem taut_apply_curried :
    PForm.Taut
      (.imp (.imp (.atom 0) (.atom 1))
        (.imp (.imp (.atom 1) (.imp (.atom 0) (.atom 2)))
          (.imp (.atom 0) (.atom 2)))) := by
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
theorem _root_.solution {Gamma : Set (Pattern S Nat)} {y : Nat}
    {p q : Pattern S Nat} (hy : y ∉ FV p) :
    Provable Gamma (.imp (Pattern.and p (.ex y q))
      (.ex y (Pattern.and p q))) := by
  let b : Pattern S Nat := Pattern.and p (.ex y q)
  let c : Pattern S Nat := Pattern.and p q
  let r : Pattern S Nat := .ex y c
  have hqbc : Provable Gamma (.imp q (.imp b c)) := by
    simpa [PForm.subst, Pattern.and, Pattern.nt, b, c] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then q else if n = 1 then p else .ex y q)
        taut_right_conj)
  have hcr : Provable Gamma (.imp c r) := by
    simpa [r, Pattern.substVar_self] using
      (Provable.exQuant (Γ := Gamma) (Pattern.captureFree_self y c))
  have hqbr : Provable Gamma (.imp q (.imp b r)) := by
    have ht : Provable Gamma
        (.imp (.imp q (.imp b c))
          (.imp (.imp c r) (.imp q (.imp b r)))) := by
      simpa [PForm.subst] using
        (Provable.taut (Γ := Gamma)
          (θ := fun n =>
            if n = 0 then q else if n = 1 then b else if n = 2 then c else r)
          taut_nested_trans)
    exact .mp hcr (.mp hqbc ht)
  have hebr : Provable Gamma (.imp (.ex y q) (.imp b r)) := by
    exact .exGen hqbr (by
      simp [b, r, c, Pattern.and, Pattern.nt, hy])
  have hbe : Provable Gamma (.imp b (.ex y q)) := by
    simpa [b] using Provable.and_elim_right Gamma p (.ex y q)
  have ht : Provable Gamma
      (.imp (.imp b (.ex y q))
        (.imp (.imp (.ex y q) (.imp b r)) (.imp b r))) := by
    simpa [PForm.subst] using
      (Provable.taut (Γ := Gamma)
        (θ := fun n => if n = 0 then b else if n = 1 then .ex y q else r)
        taut_apply_curried)
  simpa [b, r, c] using Provable.mp hebr (Provable.mp hbe ht)
end Provable
end MatchingLogic
