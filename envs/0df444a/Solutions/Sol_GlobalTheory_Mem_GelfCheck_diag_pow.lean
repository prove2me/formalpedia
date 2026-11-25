-- Prove2me | solution 1 for GlobalTheory.Mem.GelfCheck.diag_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:04:02.755393+00:00
-- url     : https://prove2.me/submissions/29195abf-17e5-49a4-8a28-078159db4f6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply
import Theorems.Thm_GlobalTheory_Mem_GelfCheck_pow_cov
import Theorems.Thm_GlobalTheory_Mem_GelfCheck_upper_kill
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
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {N : ℕ}
  {E : Matrix (Fin N) (Fin N) (Module.End R V)} {μ : Fin N → R} {v : V}
namespace GlobalTheory.Mem.GelfCheck
theorem _root_.solution (h : GlRel E) (hw : ∀ a, E a a v = μ a • v) (hv : ∀ a b, a < b → E a b v = 0) (k : ℕ)
    (a : Fin N) : (E ^ k) a a v = (∑ b, (gelfA μ ^ k) a b) • v := by
  induction k generalizing a with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    set e : Fin N → R := fun c => ∑ b, (gelfA μ ^ k) c b with he
    have ih' : ∀ c, (E ^ k) c c v = e c • v := ih
    have hr : (∑ b, (gelfA μ ^ (k+1)) a b) = ∑ c, gelfA μ a c * e c := by
      simp only [pow_succ', Matrix.mul_apply, he, Finset.mul_sum]
      exact Finset.sum_comm
    have hl : (E ^ (k+1)) a a v =
        (∑ c, (if a = c then μ a * e a else if a < c then e a - e c else 0)) • v := by
      rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply, Finset.sum_smul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rcases lt_trichotomy a c with hc | hc | hc
      · have := congrArg (fun f : Module.End R V => f v) (pow_cov h k c a a c)
        simp only [LinearMap.sub_apply, Module.End.mul_apply, hv a c hc, map_zero, sub_zero,
          if_true, ih'] at this
        simp [hc.ne, hc, this, sub_smul]
      · subst hc
        simp [ih', hw, smul_smul, mul_comm]
      · simp [upper_kill h hv k c a hc, hc.ne', not_lt.mpr hc.le]
    rw [hl, hr]
    congr 1
    have hcard : (∑ c : Fin N, if a < c then e a else 0) = ((N - 1 - a.val : ℕ) : R) * e a := by
      rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul]
    have h1 : ∀ c, (if a = c then μ a * e a else if a < c then e a - e c else 0) =
        (gelfA μ a c * e c - if a = c then ((N - 1 - a.val : ℕ) : R) * e a else 0) +
          (if a < c then e a else 0) := by
      intro c
      rcases lt_trichotomy a c with hc | hc | hc
      · simp [gelfA, hc, hc.ne]; ring
      · subst hc; simp [gelfA]; ring
      · simp [gelfA, hc.ne', not_lt.mpr hc.le]
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, hcard, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    ring
end GlobalTheory.Mem.GelfCheck
