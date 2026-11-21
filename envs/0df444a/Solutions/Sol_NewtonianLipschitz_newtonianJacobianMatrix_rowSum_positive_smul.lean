-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_rowSum_positive_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:53:24.924301+00:00
-- url     : https://prove2.me/submissions/be4119cb-ce1e-412f-a952-8421d100bbd4

module
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
public import Definitions.Def_NewtonianLipschitz_JacobianNormalization
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_entry_positive_smul


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ c : ℝ) (x : Vec3) (i : Fin 3)
    (hc : 0 < c) (hx : x ≠ 0) :
    (∑ j : Fin 3, |newtonianJacobianMatrix μ (c • x) i j|) =
      (1 / c ^ 3) *
        (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) := by
  calc
    (∑ j : Fin 3, |newtonianJacobianMatrix μ (c • x) i j|)
      = ∑ j : Fin 3,
          |(1 / c ^ 3) * newtonianJacobianMatrix μ x i j| := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [newtonianJacobianMatrix_entry_positive_smul μ c x i j hc hx]
    _ = (1 / c ^ 3) *
          (∑ j : Fin 3, |newtonianJacobianMatrix μ x i j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, abs_of_nonneg
          (by positivity : (0 : ℝ) ≤ 1 / c ^ 3)]
end NewtonianLipschitz
