-- Prove2me | solution 1 for MatchingLogic.Provable.exists_captureAvoidingSubst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:28.441217+00:00
-- url     : https://prove2.me/submissions/8463f193-2418-408c-b804-f5be73de7d75

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Theorems.Thm_MatchingLogic_Pattern_substVar_not_mem_FV_of_ne
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
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_symm
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_trans
public import Theorems.Thm_MatchingLogic_Pattern_avoidBinder_alphaEq
public import Theorems.Thm_MatchingLogic_Pattern_avoidBinder_avoids
public import Theorems.Thm_MatchingLogic_Pattern_fresh_not_mem_allVars
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
private theorem avoidBinder_not_mem_FV {y z : Nat} {p : Pattern S Nat}
    (hzp : z ∉ FV p) : z ∉ FV (avoidBinder y p) := by
  induction p with
  | var a => simpa [avoidBinder] using hzp
  | bot => simp [avoidBinder]
  | app sigma args ih =>
      simp only [avoidBinder, FV_app, Set.mem_iUnion, not_exists] at hzp ⊢
      exact fun i => ih i (hzp i)
  | imp p q ihp ihq =>
      simp only [avoidBinder, FV_imp, Set.mem_union, not_or] at hzp ⊢
      exact ⟨ihp hzp.1, ihq hzp.2⟩
  | ex a p ih =>
      simp only [avoidBinder]
      split
      · rename_i hay
        subst a
        let q := avoidBinder y p
        let w := (Pattern.ex y q).fresh
        have hwy : w ≠ y := by
          intro h
          apply (Pattern.ex y q).fresh_not_mem_allVars
          simp [w, h, Pattern.allVars]
        by_cases hzw : z = w
        · intro hzmem
          exact hzmem.2 hzw
        · by_cases hzy : z = y
          · subst z
            intro hzmem
            exact (substVar_source_not_mem_FV q (Ne.symm hwy)) hzmem.1
          · have hzbody : z ∉ FV p := by
              simpa [FV_ex, hzy] using hzp
            have hzq : z ∉ FV q := ih hzbody
            intro hzmem
            exact (substVar_not_mem_FV_of_ne (x := y) (y := w) hzw hzq) hzmem.1
      · rename_i hay
        by_cases hza : z = a
        · simp [FV_ex, hza]
        · have hzbody : z ∉ FV p := by
            simpa [FV_ex, hza] using hzp
          simpa [FV_ex, hza] using ih hzbody
private theorem not_mem_allVars_of_not_mem_FV_of_avoidsBinder {y : Nat}
    {p : Pattern S Nat} (hfree : y ∉ FV p) (havoid : AvoidsBinder y p) :
    y ∉ p.allVars := by
  induction p with
  | var z => simpa [allVars] using hfree
  | bot => simp [allVars]
  | app sigma args ih =>
      simp only [FV_app, Set.mem_iUnion, not_exists] at hfree
      simp only [allVars, Finset.mem_biUnion, Finset.mem_univ, true_and,
        not_exists]
      exact fun i => ih i (hfree i) (havoid i)
  | imp p q ihp ihq =>
      simp only [FV_imp, Set.mem_union, not_or] at hfree
      simp only [allVars, Finset.mem_union, not_or]
      exact ⟨ihp hfree.1 havoid.1, ihq hfree.2 havoid.2⟩
  | ex z p ih =>
      have hyz : y ≠ z := Ne.symm havoid.1
      have hybody : y ∉ FV p := by
        simpa [FV_ex, hyz] using hfree
      simp only [allVars, Finset.mem_insert, not_or]
      exact ⟨hyz, ih hybody havoid.2⟩
end Pattern
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
    {x y : Nat} {p : Pattern S Nat} (hy : y ∉ FV p) :
    Provable Gamma (.imp (.ex x p)
      (.ex y (Pattern.captureAvoidingSubst x y p))) := by
  let p' := Pattern.avoidBinder y p
  have hfree : y ∉ FV p' := Pattern.avoidBinder_not_mem_FV hy
  have hall : y ∉ p'.allVars :=
    Pattern.not_mem_allVars_of_not_mem_FV_of_avoidsBinder hfree
      (Pattern.avoidBinder_avoids y p)
  have halpha : Pattern.AlphaEq (.ex x p)
      (.ex y (substVar x y p')) :=
    (Pattern.AlphaEq.ex x (Pattern.avoidBinder_alphaEq y p)).trans
      (Pattern.AlphaEq.alphaEx hall)
  simpa [Pattern.captureAvoidingSubst, p'] using halpha.forward Gamma
end Provable
end MatchingLogic
