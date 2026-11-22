-- Prove2me | solution 1 for MatchingLogic.Provable.alphaEx_forward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:29.48005+00:00
-- url     : https://prove2.me/submissions/353389dd-55c4-432c-8f30-f604c22ef849

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Fresh
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Theorems.Thm_MatchingLogic_Pattern_substVar_roundtrip
public import Theorems.Thm_MatchingLogic_Pattern_captureFree_reverse_substVar
public import Theorems.Thm_MatchingLogic_Pattern_substVar_source_not_mem_FV
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
namespace MatchingLogic
namespace Provable
theorem _root_.solution {Gamma : Set (Pattern S Nat)}
    {x y : Nat} {p : Pattern S Nat} (hy : y ∉ p.allVars) :
    Provable Gamma (.imp (.ex x p) (.ex y (substVar x y p))) := by
  have hq : Provable Gamma
      (.imp (substVar y x (substVar x y p)) (.ex y (substVar x y p))) :=
    .exQuant (Pattern.captureFree_reverse_substVar hy)
  rw [Pattern.substVar_roundtrip hy] at hq
  by_cases hxy : x = y
  · subst y
    exact .exGen hq (by simp)
  · exact .exGen hq (by
      intro hx
      exact Pattern.substVar_source_not_mem_FV p hxy hx.1)
end Provable
end MatchingLogic
