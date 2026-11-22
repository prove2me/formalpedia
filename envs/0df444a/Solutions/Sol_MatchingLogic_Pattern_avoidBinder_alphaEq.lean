-- Prove2me | solution 1 for MatchingLogic.Pattern.avoidBinder_alphaEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:59.13498+00:00
-- url     : https://prove2.me/submissions/16c627c2-3757-4431-b634-decb0c63e542

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_refl
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_trans
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_alphaEx
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
public import Theorems.Thm_MatchingLogic_Pattern_fresh_not_mem_allVars
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
open scoped BigOperators
namespace MatchingLogic.Pattern
theorem _root_.solution (y : Nat) (p : Pattern S Nat) :
    AlphaEq p (avoidBinder y p) := by
  induction p with
  | var x => exact .refl _
  | bot => exact .refl _
  | app sigma args ih => exact .app ih
  | imp p q ihp ihq => exact .imp ihp ihq
  | ex z p ih =>
      simp only [avoidBinder]
      split
      · rename_i hzy
        subst z
        let w := (Pattern.ex y (avoidBinder y p)).fresh
        have hw0 := fresh_not_mem_allVars (Pattern.ex y (avoidBinder y p))
        have hw : w ∉ (avoidBinder y p).allVars := by
          intro hmem
          exact hw0 (by simp [w, allVars, hmem])
        exact (AlphaEq.ex y ih).trans (AlphaEq.alphaEx hw)
      · exact AlphaEq.ex z ih
end MatchingLogic.Pattern
