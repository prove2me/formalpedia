-- Prove2me | solution 1 for MvPolynomial.lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/361f620e-b6bf-5aeb-bc7f-92f254e9269f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul

set_option autoImplicit false

open scoped TensorProduct

namespace Ws23
namespace CoreA2

open scoped TensorProduct
open MvPolynomial

variable (R : Type*) [CommRing R] {m : ℕ}

noncomputable def contract (j : Fin m) :
    MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R →ₗ[R] MvPolynomial (Fin m) R :=
  LinearMap.mul' R (MvPolynomial (Fin m) R) ∘ₗ
    TensorProduct.map LinearMap.id
      ((pderiv j : Derivation R (MvPolynomial (Fin m) R) (MvPolynomial (Fin m) R)) :
        MvPolynomial (Fin m) R →ₗ[R] MvPolynomial (Fin m) R)

theorem contract_tmul (j : Fin m) (u v : MvPolynomial (Fin m) R) :
    contract R j (u ⊗ₜ[R] v) = u * pderiv j v := by
  simp only [contract, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.mul'_apply, Derivation.coeFn_coe]

theorem contract_mul_X_sub (j k : Fin m) (w : MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R) :
    contract R j (w * (X k ⊗ₜ[R] 1 - 1 ⊗ₜ[R] X k)) =
      -(if k = j then Algebra.TensorProduct.lmul' R w else 0) := by
  classical
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    rw [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one,
      map_sub, contract_tmul, contract_tmul, Algebra.TensorProduct.lmul'_apply_tmul, pderiv_mul, pderiv_X]
    by_cases hkj : k = j
    · subst hkj
      simp only [Pi.single_eq_same, if_true]
      ring
    · have : (Pi.single j (1 : MvPolynomial (Fin m) R) : Fin m → MvPolynomial (Fin m) R) k = 0 :=
        Pi.single_eq_of_ne hkj _
      simp only [this, if_neg hkj, mul_zero, add_zero, neg_zero]
      ring
  | add x y hx hy =>
    rw [add_mul, map_add, hx, hy, map_add]
    split_ifs <;> ring

theorem main (g : MvPolynomial (Fin m) R)
    (a : Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : g ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] g =
        ∑ j, a j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) (j : Fin m) :
    Algebra.TensorProduct.lmul' R (a j) = MvPolynomial.pderiv j g := by
  classical
  have h := congrArg (contract R j) ha
  rw [map_sub, contract_tmul, contract_tmul, pderiv_one, mul_zero, zero_sub, one_mul, map_sum] at h
  simp only [contract_mul_X_sub, Finset.sum_neg_distrib, neg_inj] at h
  rw [Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ j)] at h
  exact h.symm

end Ws23.CoreA2

theorem solution
    (R : Type*) [CommRing R] {m : ℕ} (g : MvPolynomial (Fin m) R)
    (a : Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : g ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] g =
        ∑ j, a j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) (j : Fin m) :
    Algebra.TensorProduct.lmul' R (a j) = MvPolynomial.pderiv j g :=
  Ws23.CoreA2.main R g a ha j

end S_MvPolynomial_lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul
end P2MW
export P2MW.S_MvPolynomial_lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul (solution)
