-- Prove2me | solution 1 for MatchingLogic.Pattern.substVar_roundtrip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:39.665955+00:00
-- url     : https://prove2.me/submissions/608448b8-2c58-4b3b-95c9-e029cd1c12eb

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Theorems.Thm_MatchingLogic_Pattern_substVar_eq_self_of_not_mem_allVars
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



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}
open MatchingLogic.Pattern
namespace MatchingLogic.Pattern
theorem _root_.solution {x y : Nat} {p : Pattern S Nat}
    (hy : y ∉ p.allVars) :
    substVar y x (substVar x y p) = p := by
  induction p with
  | var z =>
      simp only [allVars, Finset.mem_singleton] at hy
      by_cases hzx : z = x
      · subst z
        simp [substVar]
      · have hzy : z ≠ y := Ne.symm hy
        simp [substVar, hzx, hzy]
  | bot => rfl
  | app sigma args ih =>
      simp only [allVars, Finset.mem_biUnion, Finset.mem_univ, true_and,
        not_exists] at hy
      simp only [substVar]
      congr
      funext i
      exact ih i (hy i)
  | imp phi psi ihphi ihpsi =>
      simp only [allVars, Finset.mem_union, not_or] at hy
      simp [substVar, ihphi hy.1, ihpsi hy.2]
  | ex z phi ih =>
      simp only [allVars, Finset.mem_insert, not_or] at hy
      by_cases hzx : z = x
      · subst z
        by_cases hxy : x = y
        · subst y
          simp [substVar]
        · simp [substVar, hxy, substVar_eq_self_of_not_mem_allVars hy.2]
      · have hzy : z ≠ y := Ne.symm hy.1
        simp [substVar, hzx, hzy, ih hy.2]
end MatchingLogic.Pattern
