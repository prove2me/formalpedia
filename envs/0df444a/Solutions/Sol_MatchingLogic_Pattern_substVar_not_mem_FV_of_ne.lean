-- Prove2me | solution 1 for MatchingLogic.Pattern.substVar_not_mem_FV_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:25:01.689693+00:00
-- url     : https://prove2.me/submissions/ccce0c36-53c1-4076-984c-3a8ed70f1ca9

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
theorem _root_.solution {x y z : Nat}
    {p : Pattern S Nat} (hzy : z ≠ y) (hzp : z ∉ FV p) :
    z ∉ FV (substVar x y p) := by
  induction p with
  | var a =>
      by_cases hax : a = x <;> simp_all [substVar]
  | bot => simp [substVar]
  | app sigma args ih =>
      simp only [substVar, FV_app, Set.mem_iUnion, not_exists] at hzp ⊢
      exact fun i => ih i (hzp i)
  | imp p q ihp ihq =>
      simp only [substVar, FV_imp, Set.mem_union, not_or] at hzp ⊢
      exact ⟨ihp hzp.1, ihq hzp.2⟩
  | ex a p ih =>
      by_cases hax : a = x
      · simpa [substVar, hax] using hzp
      · simp only [substVar, if_neg hax]
        by_cases hza : z = a
        · simp [FV_ex, hza]
        · have hzbody : z ∉ FV p := by
            simpa [FV_ex, hza] using hzp
          simpa [FV_ex, hza] using ih hzbody
end MatchingLogic.Pattern
