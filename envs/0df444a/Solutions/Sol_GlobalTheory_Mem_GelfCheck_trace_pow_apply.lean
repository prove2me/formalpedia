-- Prove2me | solution 1 for GlobalTheory.Mem.GelfCheck.trace_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:07.356804+00:00
-- url     : https://prove2.me/submissions/917c44b8-ff3a-414d-9e5c-63935b28b35c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply
import Theorems.Thm_GlobalTheory_Mem_GelfCheck_pow_cov
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
open MvPolynomial
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {N : ℕ}
  {E : Matrix (Fin N) (Fin N) (Module.End R V)} {μ : Fin N → R} {v : V}
namespace GlobalTheory.Mem.GelfCheck
namespace _root_.GlobalTheory.Mem.GelfCheck
theorem _root_.solution (h : _root_.GlobalTheory.Mem.Gelf.GlRel E)
    (hw : ∀ a, E a a v = μ a • v) (hv : ∀ a b, a < b → E a b v = 0)
    (k : ℕ) : (E ^ k).trace v = _root_.GlobalTheory.Mem.Gelf.gelfC μ k • v := by
  have main : ∀ k : ℕ, (∀ a b : Fin N, a < b → (E ^ k) a b v = 0) ∧
      ∀ a, (E ^ k) a a v = (∑ b, (_root_.GlobalTheory.Mem.Gelf.gelfA μ ^ k) a b) • v := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun a b hab => ?_, fun a => ?_⟩
      · simp [Matrix.one_apply, hab.ne]
      · simp [Matrix.one_apply]
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have expand : ∀ a b, (E ^ (k + 1)) a b v = ∑ m, (E ^ k) a m (E m b v) := by
        intro a b
        simp [pow_succ, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply]
      have term : ∀ a b m, a ≤ b → (E ^ k) a m (E m b v) =
          if m < b then 0 else if m = b then μ b • (E ^ k) a b v
            else (E ^ k) a b v - (if b = a then (E ^ k) m m v else 0) := by
        intro a b m hab
        rcases lt_trichotomy m b with hmb | hmb | hmb
        · simp [hmb, hv m b hmb]
        · subst hmb
          simp [hw]
        · have hc := congrArg (fun f : Module.End R V => f v)
            (_root_.GlobalTheory.Mem.GelfCheck.pow_cov h k a m m b)
          simp only [LinearMap.sub_apply, Module.End.mul_apply, if_pos rfl] at hc
          rw [ih1 a m (lt_of_le_of_lt hab hmb), map_zero, zero_sub] at hc
          rw [if_neg (not_lt.mpr hmb.le), if_neg hmb.ne', ← neg_neg ((E ^ k) a m (E m b v)), hc]
          split_ifs <;> simp
      refine ⟨fun a b hab => ?_, fun a => ?_⟩
      · rw [expand, Finset.sum_congr rfl fun m _ => term a b m hab.le, ih1 a b hab]
        simp [hab.ne']
      · rw [expand, Finset.sum_congr rfl fun m _ => term a a m le_rfl]
        obtain ⟨s, hs_def⟩ : ∃ s : Fin N → R,
            s = fun m => ∑ b, (_root_.GlobalTheory.Mem.Gelf.gelfA μ ^ k) m b := ⟨_, rfl⟩
        have ih2' : ∀ m, (E ^ k) m m v = s m • v := by
          intro m
          rw [ih2, hs_def]
        have hs : ∑ b, (_root_.GlobalTheory.Mem.Gelf.gelfA μ ^ (k + 1)) a b =
            ∑ m, _root_.GlobalTheory.Mem.Gelf.gelfA μ a m * s m := by
          simp only [hs_def, pow_succ', Matrix.mul_apply, Finset.mul_sum]
          exact Finset.sum_comm
        have hterm : ∀ m, (if m < a then 0 else if m = a then μ a • (E ^ k) a a v
            else (E ^ k) a a v - (if a = a then (E ^ k) m m v else 0)) =
            (_root_.GlobalTheory.Mem.Gelf.gelfA μ a m * s m) • v +
              ((if a < m then s a else 0) -
                (if m = a then ((N - 1 - a.val : ℕ) : R) * s a else 0)) • v := by
          intro m
          rw [ih2', ih2', if_pos rfl]
          rcases lt_trichotomy m a with hma | hma | hma
          · simp [_root_.GlobalTheory.Mem.Gelf.gelfA, hma, hma.ne', not_lt.mpr hma.le, hma.ne]
          · subst hma
            have hdiag : _root_.GlobalTheory.Mem.Gelf.gelfA μ m m = μ m + ((N - 1 - m.val : ℕ) : R) := by
              simp [_root_.GlobalTheory.Mem.Gelf.gelfA]
            rw [hdiag, if_neg (lt_irrefl m), if_pos rfl, if_neg (lt_irrefl m), if_pos rfl]
            module
          · have hup : _root_.GlobalTheory.Mem.Gelf.gelfA μ a m = -1 := by
              simp [_root_.GlobalTheory.Mem.Gelf.gelfA, hma.ne, hma]
            rw [hup, if_neg (not_lt.mpr hma.le), if_neg hma.ne', if_pos hma, if_neg hma.ne']
            module
        have hf : (Finset.univ.filter fun m : Fin N => a < m) = Finset.Ioi a := by
          ext m
          simp
        have hc : ∑ m : Fin N, (if a < m then s a else 0) = ((N - 1 - a.val : ℕ) : R) * s a := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hf, Fin.card_Ioi]
        rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_add_distrib, ← Finset.sum_smul,
          ← Finset.sum_smul, Finset.sum_sub_distrib, hc, Finset.sum_ite_eq',
          if_pos (Finset.mem_univ a), sub_self, zero_smul, add_zero, hs]
  simp only [Matrix.trace, Matrix.diag, LinearMap.sum_apply, (main k).2,
    _root_.GlobalTheory.Mem.Gelf.gelfC, Finset.sum_smul]
end _root_.GlobalTheory.Mem.GelfCheck
end GlobalTheory.Mem.GelfCheck
