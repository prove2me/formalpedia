-- Prove2me | solution 1 for MatchingLogic.locConsistent_insert_captureAvoidingWitness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:28.012806+00:00
-- url     : https://prove2.me/submissions/686764d0-d877-4bdb-91ea-872c7233baf6

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Mathlib.Data.Countable.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Theorems.Thm_MatchingLogic_LocProvable_not_ex_of_not_fresh
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_LocProvable_deduction_insert
public import Theorems.Thm_MatchingLogic_LocProvable_mp
public import Theorems.Thm_MatchingLogic_LocProvable_of_provable
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Pattern_captureAvoidingSubst_eq_substVar_of_fresh
public import Theorems.Thm_MatchingLogic_Provable_alphaEx_forward
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
open Set
variable {S : Signature}
noncomputable section
private theorem not_imp_left_taut :
    PForm.Taut
      (.imp (.imp (.imp (.atom 0) (.atom 1)) .bot) (.atom 0)) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]
private theorem not_imp_right_taut :
    PForm.Taut
      (.imp (.imp (.imp (.atom 0) (.atom 1)) .bot)
        (.imp (.atom 1) .bot)) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]
private theorem Provable.not_imp_left (Gamma : Set (Pattern S Nat))
    (p q : Pattern S Nat) :
    Provable Gamma (.imp (Pattern.nt (.imp p q)) p) := by
  simpa [PForm.subst, Pattern.nt] using
    (Provable.taut (Γ := Gamma) (θ := fun n => if n = 0 then p else q)
      not_imp_left_taut)
private theorem Provable.not_imp_right (Gamma : Set (Pattern S Nat))
    (p q : Pattern S Nat) :
    Provable Gamma (.imp (Pattern.nt (.imp p q)) (Pattern.nt q)) := by
  simpa [PForm.subst, Pattern.nt] using
    (Provable.taut (Γ := Gamma) (θ := fun n => if n = 0 then p else q)
      not_imp_right_taut)
end
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open Set
variable {S : Signature}
noncomputable section
attribute [local instance] MatchingLogic.instDecidableEqPatternNatWitnessed
namespace MatchingLogic
theorem _root_.solution
    {Gamma : Set (Pattern S Nat)} {x y : Nat} {p : Pattern S Nat}
    (hGamma : LocConsistent Gamma)
    (hyGamma : ∀ q ∈ Gamma, y ∉ FV q)
    (hyp : y ∉ p.allVars) :
    LocConsistent
      (insert (.imp (.ex x p) (Pattern.captureAvoidingSubst x y p)) Gamma) := by
  intro hbad
  let q := Pattern.captureAvoidingSubst x y p
  let e : Pattern S Nat := .ex x p
  have hnimp : LocProvable Gamma (Pattern.nt (.imp e q)) := by
    simpa [e, q] using LocProvable.deduction_insert hbad
  have he : LocProvable Gamma e :=
    hnimp.mp (LocProvable.of_provable (Provable.not_imp_left ∅ e q))
  have hnq : LocProvable Gamma (Pattern.nt q) :=
    hnimp.mp (LocProvable.of_provable (Provable.not_imp_right ∅ e q))
  have hnex : LocProvable Gamma (Pattern.nt (.ex y q)) :=
    hnq.not_ex_of_not_fresh hyGamma
  have halpha : Provable (∅ : Set (Pattern S Nat)) (.imp e (.ex y q)) := by
    have hraw := Provable.alphaEx_forward (Gamma := (∅ : Set (Pattern S Nat)))
      (x := x) (p := p) hyp
    simpa [e, q, Pattern.captureAvoidingSubst_eq_substVar_of_fresh hyp] using hraw
  have hex : LocProvable Gamma (.ex y q) :=
    he.mp (LocProvable.of_provable halpha)
  exact hGamma (hex.mp hnex)
end MatchingLogic
