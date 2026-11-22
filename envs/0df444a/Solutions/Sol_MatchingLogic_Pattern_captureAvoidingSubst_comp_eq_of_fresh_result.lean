-- Prove2me | solution 1 for MatchingLogic.Pattern.captureAvoidingSubst_comp_eq_of_fresh_result
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:44.160487+00:00
-- url     : https://prove2.me/submissions/8a0af90b-8879-46cc-805c-6cc5abff7153

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessPush
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FreshWitnessElim
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
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_symm
public import Theorems.Thm_MatchingLogic_Pattern_avoidBinder_eq_self_of_not_mem_allVars
public import Theorems.Thm_MatchingLogic_Pattern_captureAvoidingSubst_eq_substVar_of_fresh
public import Theorems.Thm_MatchingLogic_Pattern_substVar_eq_self_of_not_mem_allVars
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
private theorem allVars_substVar_mem {x y z : Nat} {p : Pattern S Nat}
    (hz : z ∈ (substVar x y p).allVars) : z = y ∨ z ∈ p.allVars := by
  induction p with
  | var a =>
      by_cases hax : a = x
      · subst a
        exact Or.inl (by simpa [substVar, allVars] using hz)
      · simpa [substVar, allVars, hax] using Or.inr hz
  | bot => simp [substVar, allVars] at hz
  | app sigma args ih =>
      simp only [substVar, allVars, Finset.mem_biUnion, Finset.mem_univ, true_and] at hz ⊢
      rcases hz with ⟨i, hi⟩
      rcases ih i hi with hzy | hmem
      · exact Or.inl hzy
      · exact Or.inr ⟨i, hmem⟩
  | imp p q ihp ihq =>
      simp only [substVar, allVars, Finset.mem_union] at hz ⊢
      rcases hz with hp | hq
      · rcases ihp hp with hzy | hmem
        · exact Or.inl hzy
        · exact Or.inr (Or.inl hmem)
      · rcases ihq hq with hzy | hmem
        · exact Or.inl hzy
        · exact Or.inr (Or.inr hmem)
  | ex a p ih =>
      by_cases hax : a = x
      · subst a
        simp only [substVar, if_pos, allVars, Finset.mem_insert] at hz ⊢
        exact Or.inr hz
      · simp only [substVar, if_neg hax, allVars, Finset.mem_insert] at hz ⊢
        rcases hz with hza | hz
        · exact Or.inr (Or.inl hza)
        · rcases ih hz with hzy | hmem
          · exact Or.inl hzy
          · exact Or.inr (Or.inr hmem)
private theorem substVar_not_mem_allVars_of_ne {x y z : Nat} {p : Pattern S Nat}
    (hzy : z ≠ y) (hz : z ∉ p.allVars) : z ∉ (substVar x y p).allVars := by
  intro h
  rcases allVars_substVar_mem h with hEq | hp
  · exact hzy hEq
  · exact hz hp
private theorem substVar_comp_of_fresh {x y z : Nat} {p : Pattern S Nat}
    (hy : y ∉ p.allVars) :
    substVar y z (substVar x y p) = substVar x z p := by
  induction p with
  | var a =>
      simp only [allVars, Finset.mem_singleton] at hy
      have hay : a ≠ y := Ne.symm hy
      by_cases hax : a = x <;> simp [substVar, hax, hay]
  | bot => rfl
  | app sigma args ih =>
      simp only [allVars, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hy
      simp only [substVar]
      congr
      funext i
      exact ih i (hy i)
  | imp p q ihp ihq =>
      simp only [allVars, Finset.mem_union, not_or] at hy
      simp [substVar, ihp hy.1, ihq hy.2]
  | ex a p ih =>
      simp only [allVars, Finset.mem_insert, not_or] at hy
      by_cases hax : a = x
      · subst a
        have hxy : x ≠ y := Ne.symm hy.1
        simp only [substVar, if_pos, if_neg hxy]
        rw [Pattern.substVar_eq_self_of_not_mem_allVars hy.2]
      · have hay : a ≠ y := Ne.symm hy.1
        simp [substVar, hax, hay, ih hy.2]
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
open MatchingLogic.Pattern
namespace MatchingLogic.Pattern
theorem _root_.solution {x y z : Nat}
    {p : Pattern S Nat} (hy : y ∉ p.allVars) (hz : z ∉ p.allVars)
    (hzs : z ∉ (substVar x y p).allVars) :
    captureAvoidingSubst y z (captureAvoidingSubst x y p) =
      captureAvoidingSubst x z p := by
  by_cases hzy : z = y
  · subst z
    rw [captureAvoidingSubst_eq_substVar_of_fresh hy]
    simp only [captureAvoidingSubst, avoidBinder_eq_self_of_not_mem_allVars hzs]
    exact Pattern.substVar_eq_self_of_not_mem_allVars hzs
  · rw [captureAvoidingSubst_eq_substVar_of_fresh hy]
    rw [captureAvoidingSubst_eq_substVar_of_fresh
      (substVar_not_mem_allVars_of_ne hzy hz)]
    rw [captureAvoidingSubst_eq_substVar_of_fresh hz]
    exact substVar_comp_of_fresh hy
end MatchingLogic.Pattern
