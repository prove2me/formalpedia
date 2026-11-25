-- Prove2me | solution 1 for MvPolyLaplacian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:36:33.462904+00:00
-- url     : https://prove2.me/submissions/30354e20-de3d-4624-87d8-59a0fa67c07c

module
public import Definitions.Def_PHarmonicPoly_MvPolyHessian
public import Definitions.Def_PHarmonicPoly_MvPolyLaplacian
public import Theorems.Thm_MvPolyHessian


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian
        (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x
      = ∑ i, MvPolynomial.eval (fun j => x j) (pderiv i (pderiv i P)) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MvPolyHessian P x _ _]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; simp at h
  · intro i _ hi
    refine Finset.sum_eq_zero (fun j _ => ?_)
    simp [hi]
  · intro h; simp at h
