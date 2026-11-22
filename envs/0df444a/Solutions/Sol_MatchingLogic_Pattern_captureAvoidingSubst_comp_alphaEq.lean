-- Prove2me | solution 1 for MatchingLogic.Pattern.captureAvoidingSubst_comp_alphaEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:12.621815+00:00
-- url     : https://prove2.me/submissions/b7c4d030-a15f-414e-bfbf-9769b38cefda

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FreshWitnessElim
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessElim
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
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_alphaEx
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_refl
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_symm
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_trans
public import Theorems.Thm_MatchingLogic_Pattern_fresh_not_mem_allVars
public import Theorems.Thm_MatchingLogic_Pattern_substVar_eq_self_of_not_mem_FV
public import Theorems.Thm_MatchingLogic_Pattern_substVar_not_mem_FV_of_ne
public import Theorems.Thm_MatchingLogic_Pattern_substVar_source_not_mem_FV
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
private theorem avoidTwo_avoids (y z : Nat) (p : Pattern S Nat) :
    AvoidsBinder y (avoidTwo y z p) ∧ AvoidsBinder z (avoidTwo y z p) := by
  induction p with
  | var a => exact ⟨trivial, trivial⟩
  | bot => exact ⟨trivial, trivial⟩
  | app sigma args ih => exact ⟨fun i => (ih i).1, fun i => (ih i).2⟩
  | imp p q ihp ihq => exact ⟨⟨ihp.1, ihq.1⟩, ⟨ihp.2, ihq.2⟩⟩
  | ex a p ih =>
      simp only [avoidTwo]
      split
      · let q := avoidTwo y z p
        let w := (Pattern.imp (Pattern.var y)
          (Pattern.imp (Pattern.var z) (Pattern.ex a q))).fresh
        have hw0 := (Pattern.imp (Pattern.var y)
          (Pattern.imp (Pattern.var z) (Pattern.ex a q))).fresh_not_mem_allVars
        have hwy : w ≠ y := by
          intro h
          apply hw0
          simp [w, h, allVars]
        have hwz : w ≠ z := by
          intro h
          apply hw0
          simp [w, h, allVars]
        exact ⟨⟨hwy, ih.1.substVar⟩, ⟨hwz, ih.2.substVar⟩⟩
      · rename_i hnot
        exact ⟨⟨fun h => hnot (Or.inl h), ih.1⟩,
          ⟨fun h => hnot (Or.inr h), ih.2⟩⟩
private theorem avoidTwo_alphaEq (y z : Nat) (p : Pattern S Nat) :
    AlphaEq p (avoidTwo y z p) := by
  induction p with
  | var a => exact .refl _
  | bot => exact .refl _
  | app sigma args ih => exact .app ih
  | imp p q ihp ihq => exact .imp ihp ihq
  | ex a p ih =>
      simp only [avoidTwo]
      split
      · let q := avoidTwo y z p
        let w := (Pattern.imp (Pattern.var y)
          (Pattern.imp (Pattern.var z) (Pattern.ex a q))).fresh
        have hw0 := (Pattern.imp (Pattern.var y)
          (Pattern.imp (Pattern.var z) (Pattern.ex a q))).fresh_not_mem_allVars
        have hwq : w ∉ q.allVars := by
          intro h
          apply hw0
          simp [w, allVars, h]
        exact (AlphaEq.ex a ih).trans (AlphaEq.alphaEx hwq)
      · exact AlphaEq.ex a ih
private theorem avoidTwo_not_mem_FV {y z : Nat} {p : Pattern S Nat}
    (hy : y ∉ FV p) : y ∉ FV (avoidTwo y z p) := by
  induction p with
  | var a => simpa [avoidTwo] using hy
  | bot => simp [avoidTwo]
  | app sigma args ih =>
      simp only [FV_app, Set.mem_iUnion, not_exists] at hy
      simp only [avoidTwo, FV_app, Set.mem_iUnion, not_exists]
      exact fun i => ih i (hy i)
  | imp p q ihp ihq =>
      simp only [FV_imp, Set.mem_union, not_or] at hy
      simp only [avoidTwo, FV_imp, Set.mem_union, not_or]
      exact ⟨ihp hy.1, ihq hy.2⟩
  | ex a p ih =>
      simp only [avoidTwo]
      split
      · rename_i hrename
        let q := avoidTwo y z p
        let w := (Pattern.imp (Pattern.var y)
          (Pattern.imp (Pattern.var z) (Pattern.ex a q))).fresh
        have hw0 := (Pattern.imp (Pattern.var y)
          (Pattern.imp (Pattern.var z) (Pattern.ex a q))).fresh_not_mem_allVars
        have hwy : w ≠ y := by
          intro h
          apply hw0
          simp [w, h, allVars]
        by_cases hay : a = y
        · subst a
          intro hmem
          exact (substVar_source_not_mem_FV q (Ne.symm hwy)) hmem.1
        · have hyp : y ∉ FV p := by simpa [FV_ex, Ne.symm hay] using hy
          have hyq := ih hyp
          intro hmem
          exact (substVar_not_mem_FV_of_ne (x := a) (y := w)
            (z := y)
            (Ne.symm hwy) hyq) hmem.1
      · rename_i hnot
        have hay : a ≠ y := fun h => hnot (Or.inl h)
        have hyp : y ∉ FV p := by simpa [FV_ex, Ne.symm hay] using hy
        simpa [FV_ex, Ne.symm hay] using ih hyp
private theorem avoidBinder_eq_self_of_avoids {t : Nat} {p : Pattern S Nat}
    (h : AvoidsBinder t p) : avoidBinder t p = p := by
  induction p with
  | var a => rfl
  | bot => rfl
  | app sigma args ih =>
      simp only [avoidBinder]
      congr
      funext i
      exact ih i (h i)
  | imp p q ihp ihq => simp [avoidBinder, ihp h.1, ihq h.2]
  | ex a p ih => simp [avoidBinder, h.1, ih h.2]
private theorem substVar_comp_of_fresh {x y z : Nat} {p : Pattern S Nat}
    (hy : y ∉ FV p) (hay : AvoidsBinder y p) (haz : AvoidsBinder z p) :
    substVar y z (substVar x y p) = substVar x z p := by
  induction p with
  | var a =>
      simp only [FV_var, Set.mem_singleton_iff] at hy
      by_cases hax : a = x <;> simp [substVar, hax, Ne.symm hy]
  | bot => rfl
  | app sigma args ih =>
      simp only [FV_app, Set.mem_iUnion, not_exists] at hy
      simp only [substVar]
      congr
      funext i
      exact ih i (hy i) (hay i) (haz i)
  | imp p q ihp ihq =>
      simp only [FV_imp, Set.mem_union, not_or] at hy
      simp [substVar, ihp hy.1 hay.1 haz.1, ihq hy.2 hay.2 haz.2]
  | ex a p ih =>
      have hay' : a ≠ y := hay.1
      have haz' : a ≠ z := haz.1
      have hyp : y ∉ FV p := by simpa [FV_ex, Ne.symm hay'] using hy
      by_cases hax : a = x
      · subst a
        have hself := substVar_eq_self_of_not_mem_FV (x := y) (y := z) hyp
        simp [substVar, hself]
      · simp [substVar, hax, hay', ih hyp hay.2 haz.2]
end Pattern
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern
namespace MatchingLogic.Pattern
theorem _root_.solution {x y z : Nat}
    {p : Pattern S Nat} (hy : y ∉ FV p) :
    AlphaEq
      (captureAvoidingSubst y z (captureAvoidingSubst x y p))
      (captureAvoidingSubst x z p) := by
  let q := avoidTwo y z p
  have halpha : AlphaEq p q := avoidTwo_alphaEq y z p
  have hqy : y ∉ FV q := avoidTwo_not_mem_FV hy
  have havoids := avoidTwo_avoids y z p
  have hleft : AlphaEq
      (captureAvoidingSubst y z (captureAvoidingSubst x y p))
      (captureAvoidingSubst y z (captureAvoidingSubst x y q)) :=
    (halpha.captureAvoidingSubst x y).captureAvoidingSubst y z
  have hright : AlphaEq (captureAvoidingSubst x z p)
      (captureAvoidingSubst x z q) := halpha.captureAvoidingSubst x z
  have hraw : substVar y z (substVar x y q) = substVar x z q :=
    substVar_comp_of_fresh hqy havoids.1 havoids.2
  have hmid : AlphaEq
      (captureAvoidingSubst y z (captureAvoidingSubst x y q))
      (captureAvoidingSubst x z q) := by
    have hby : avoidBinder y q = q := avoidBinder_eq_self_of_avoids havoids.1
    have hbz : avoidBinder z q = q := avoidBinder_eq_self_of_avoids havoids.2
    have hbzs : avoidBinder z (substVar x y q) = substVar x y q :=
      avoidBinder_eq_self_of_avoids havoids.2.substVar
    change AlphaEq
      (substVar y z (avoidBinder z (substVar x y (avoidBinder y q))))
      (substVar x z (avoidBinder z q))
    rw [hby, hbz, hbzs, hraw]
    exact AlphaEq.refl _
  exact hleft.trans (hmid.trans hright.symm)
end MatchingLogic.Pattern
