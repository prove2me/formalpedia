-- Prove2me | solution 1 for GlobalTheory.Mem.GelfCheck.glRel_rowE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:11.131108+00:00
-- url     : https://prove2.me/submissions/690b2e49-c9b7-447f-be47-24170041493e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply
import Theorems.Thm_GlobalTheory_Mem_GelfCheck_rowE_X
import Theorems.Thm_GlobalTheory_Mem_GelfCheck_rowE_mul
import Theorems.Thm_GlobalTheory_Mem_GelfCheck_rowE_C
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GelfCheck
open MvPolynomial GlobalTheory.Mem.Gelf
open MvPolynomial
namespace GlobalTheory.Mem.GelfCheck
namespace _root_.GlobalTheory.Mem.GelfCheck
theorem _root_.solution (R : Type) [CommRing R] (r n : ℕ) :
    _root_.GlobalTheory.Mem.Gelf.GlRel (_root_.GlobalTheory.Mem.Gelf.rowE R r n) := by
  intro a b c d
  set E := _root_.GlobalTheory.Mem.Gelf.rowE R r n with hE
  apply LinearMap.ext
  intro P
  induction P using MvPolynomial.induction_on with
  | C x =>
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hE, _root_.GlobalTheory.Mem.GelfCheck.rowE_C,
      map_zero, sub_zero]
    split_ifs <;> simp [_root_.GlobalTheory.Mem.GelfCheck.rowE_C]
  | add p q hp hq =>
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    obtain ⟨e, t⟩ := v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hp ⊢
    simp only [hE, _root_.GlobalTheory.Mem.GelfCheck.rowE_mul, map_add, _root_.GlobalTheory.Mem.GelfCheck.rowE_X,
      apply_ite, map_zero] at hp ⊢
    split_ifs at hp ⊢ <;> subst_vars <;>
      simp_all [_root_.GlobalTheory.Mem.GelfCheck.rowE_mul, _root_.GlobalTheory.Mem.GelfCheck.rowE_X] <;>
      linear_combination hp * X _
end _root_.GlobalTheory.Mem.GelfCheck
end GlobalTheory.Mem.GelfCheck
