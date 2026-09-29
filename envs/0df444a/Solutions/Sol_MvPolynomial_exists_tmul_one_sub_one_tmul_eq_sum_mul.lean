-- Prove2me | solution 1 for MvPolynomial.exists_tmul_one_sub_one_tmul_eq_sum_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/2478ccdc-706d-50c2-ab7a-2779a2da7766

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_exists_tmul_one_sub_one_tmul_eq_sum_mul

set_option autoImplicit false

open scoped TensorProduct

namespace Ws23
namespace CoreA1

open scoped TensorProduct
open MvPolynomial

theorem main (R : Type*) [CommRing R] {m : ℕ} (g : MvPolynomial (Fin m) R) :
    ∃ a : Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R,
      g ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] g =
        ∑ j, a j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j) := by
  classical
  induction g using MvPolynomial.induction_on with
  | C r =>

    refine ⟨0, ?_⟩
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    rw [sub_eq_zero, MvPolynomial.C_eq_smul_one, TensorProduct.smul_tmul]
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b, ?_⟩
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ← ha, ← hb, TensorProduct.add_tmul,
      TensorProduct.tmul_add]
    abel
  | mul_X p n hp =>
    obtain ⟨a, ha⟩ := hp

    refine ⟨fun k => a k * (X n ⊗ₜ[R] 1) + if k = n then (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] p else 0, ?_⟩
    have key : (p * X n) ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] (p * X n) =
        (p ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] p) * (X n ⊗ₜ[R] 1) +
          ((1 : MvPolynomial (Fin m) R) ⊗ₜ[R] p) * (X n ⊗ₜ[R] 1 - 1 ⊗ₜ[R] X n) := by
      simp only [sub_mul, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      abel
    rw [key, ha, Finset.sum_mul]
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      ring
    · simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Ws23.CoreA1

theorem solution
    (R : Type*) [CommRing R] {m : ℕ} (g : MvPolynomial (Fin m) R) :
    ∃ a : Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R,
      g ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] g =
        ∑ j, a j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j) :=
  Ws23.CoreA1.main R g

end S_MvPolynomial_exists_tmul_one_sub_one_tmul_eq_sum_mul
end P2MW
export P2MW.S_MvPolynomial_exists_tmul_one_sub_one_tmul_eq_sum_mul (solution)
