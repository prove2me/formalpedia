-- Prove2me | solution 1 for MatchingLogic.Pattern.captureAvoidingSubst_not_mem_FV_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:38.495059+00:00
-- url     : https://prove2.me/submissions/90656a1d-2f27-4738-995f-d0288a8f2e4b

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
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_symm
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
    {p : Pattern S Nat} (hzy : z ≠ y) (hzp : z ∉ FV p) :
    z ∉ FV (captureAvoidingSubst x y p) := by
  exact substVar_not_mem_FV_of_ne hzy (avoidBinder_not_mem_FV hzp)
end MatchingLogic.Pattern
