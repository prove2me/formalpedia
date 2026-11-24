-- Prove2me | solution 1 for GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:00.593342+00:00
-- url     : https://prove2.me/submissions/54f52962-bb7c-446e-8eda-332c4d24f550

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply
import Theorems.Thm_GlobalTheory_Mem_GelfCheck_rowE_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
noncomputable section
namespace GlobalTheory.Mem.GelfCheck
open MvPolynomial GlobalTheory.Mem.Gelf
open MvPolynomial in
private theorem gradedWeyl_gen_coeff_one_and_coeff_zero (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r)
    (P : MvPolynomial (Fin r × Fin n) R) :
    (_root_.Formalism.GradedWeylDivisibility.rowGen R a b P).coeff 1 = ∑ s : Fin n, X (a, s) * pderiv (b, s) P ∧
      (_root_.Formalism.GradedWeylDivisibility.rowGen R a b P).coeff 0 = P := by
  induction P using MvPolynomial.induction_on with
  | C x =>
    simp [_root_.Formalism.GradedWeylDivisibility.rowGen, Polynomial.coeff_C]
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, hp.1, hp.2, hq.1, hq.2, Finset.sum_add_distrib,
      mul_add, and_self]
  | mul_X p v hp =>
    obtain ⟨hp1, hp0⟩ := hp
    have hX : _root_.Formalism.GradedWeylDivisibility.rowGen R a b (X v) = Polynomial.C (X v) +
        if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0 := by
      simp [_root_.Formalism.GradedWeylDivisibility.rowGen]
    rw [map_mul, hX]
    obtain ⟨i, t⟩ := v
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    split_ifs with hib
    · subst hib
      have h1 : (1 : ℕ) = 0 + 1 := rfl
      rw [← mul_assoc]
      simp only [Polynomial.coeff_add, Polynomial.coeff_mul_C]
      rw [h1, Polynomial.coeff_mul_X, ← h1]
      simp only [Polynomial.coeff_mul_X_zero, zero_mul, add_zero, hp0, hp1]
      refine ⟨?_, trivial⟩
      simp only [Pi.single_apply, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
      rw [add_comm]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun _ _ => by ring
    · simp [Pi.single_apply, Prod.ext_iff, hib, Polynomial.coeff_mul_C, hp0, hp1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
section
variable {A : Type} [Ring A] {N : ℕ} {E : Matrix (Fin N) (Fin N) A}
end
section
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {N : ℕ}
  {E : Matrix (Fin N) (Fin N) (Module.End R V)} {μ : Fin N → R} {v : V}
end
example : gelfC (![1, 0] : Fin 2 → ℤ) 2 = 2 := by
  simp [gelfC, gelfA, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
example : gelfC (![0, 1] : Fin 2 → ℤ) 2 = 0 := by
  simp [gelfC, gelfA, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
end GlobalTheory.Mem.GelfCheck
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GelfCheck
open MvPolynomial GlobalTheory.Mem.Gelf
open MvPolynomial
namespace GlobalTheory.Mem.GelfCheck
namespace _root_.GlobalTheory.Mem.GelfCheck
theorem _root_.solution (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r)
    (P : MvPolynomial (Fin r × Fin n) R) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b P = _root_.Formalism.GradedWeylDivisibility.rowDiv R a b 1 P ∧ _root_.Formalism.GradedWeylDivisibility.rowDiv R a b 0 P = P := by
  obtain ⟨h1, h0⟩ := gradedWeyl_gen_coeff_one_and_coeff_zero R r n a b P
  rw [_root_.GlobalTheory.Mem.GelfCheck.rowE_apply]
  exact ⟨by unfold _root_.Formalism.GradedWeylDivisibility.rowDiv; exact h1.symm, by unfold _root_.Formalism.GradedWeylDivisibility.rowDiv; exact h0⟩
end _root_.GlobalTheory.Mem.GelfCheck
end GlobalTheory.Mem.GelfCheck
