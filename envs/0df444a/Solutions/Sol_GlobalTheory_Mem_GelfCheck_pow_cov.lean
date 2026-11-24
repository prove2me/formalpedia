-- Prove2me | solution 1 for GlobalTheory.Mem.GelfCheck.pow_cov
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:28.568889+00:00
-- url     : https://prove2.me/submissions/5b1fd0ae-351e-46bc-90f3-91998413eb25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply
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
variable {A : Type} [Ring A] {N : ℕ} {E : Matrix (Fin N) (Fin N) A}
open MvPolynomial
variable {A : Type} [Ring A] {N : ℕ} {E : Matrix (Fin N) (Fin N) A}
namespace GlobalTheory.Mem.GelfCheck
namespace _root_.GlobalTheory.Mem.GelfCheck
theorem _root_.solution (h : _root_.GlobalTheory.Mem.Gelf.GlRel E) (k : ℕ)
    (a b c d : Fin N) :
    E c d * (E ^ k) a b - (E ^ k) a b * E c d =
      (if d = a then (E ^ k) c b else 0) - (if b = c then (E ^ k) a d else 0) := by
  induction k generalizing a b with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> subst_vars <;> simp_all
  | succ k ih =>
    have key : ∀ m, E c d * ((E ^ k) a m * E m b) - (E ^ k) a m * E m b * E c d =
        ((if d = a then (E ^ k) c m * E m b else 0) - (if m = c then (E ^ k) a d * E m b else 0)) +
        ((if d = m then (E ^ k) a m * E c b else 0) - (if b = c then (E ^ k) a m * E m d else 0)) := by
      intro m
      have h1 := ih a m
      have h2 := h c d m b
      rw [show E c d * ((E ^ k) a m * E m b) - (E ^ k) a m * E m b * E c d =
        (E c d * (E ^ k) a m - (E ^ k) a m * E c d) * E m b +
          (E ^ k) a m * (E c d * E m b - E m b * E c d) by noncomm_ring, h1, h2]
      simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl fun m _ => key m]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    split_ifs <;> simp <;> abel
end _root_.GlobalTheory.Mem.GelfCheck
end GlobalTheory.Mem.GelfCheck
