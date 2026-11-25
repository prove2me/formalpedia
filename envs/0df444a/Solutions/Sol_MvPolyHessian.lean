-- Prove2me | solution 1 for MvPolyHessian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:24:38.10772+00:00
-- url     : https://prove2.me/submissions/0d8cab2c-75f0-4125-b556-a0a1b83bcafe

module
public import Definitions.Def_PHarmonicPoly_MvPolyGradient
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Definitions.Def_PHarmonicPoly_MvPolyHessian
public import Theorems.Thm_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyGradient


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x v w : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ 2
        (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x ![v, w]
      = ∑ i, ∑ j, v i * w j * MvPolynomial.eval (fun k => x k) (pderiv i (pderiv j P)) := by
  have hfd : fderiv ℝ
      (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => z i) P)
      = fun y : EuclideanSpace ℝ (Fin n) =>
        ∑ i, (MvPolynomial.eval (fun j => y j) (pderiv i P)) •
          (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
    funext y
    exact (MvPolyFDerivEuclidean P y).fderiv
  have hG : HasFDerivAt
      (fun y : EuclideanSpace ℝ (Fin n) =>
        ∑ i, (MvPolynomial.eval (fun j => y j) (pderiv i P)) •
          (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      (∑ i, (∑ j, (MvPolynomial.eval (fun k => x k) (pderiv j (pderiv i P))) •
          (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).smulRight
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) x := by
    have hterm : ∀ i : Fin n, HasFDerivAt
        (fun y : EuclideanSpace ℝ (Fin n) =>
          (MvPolynomial.eval (fun j => y j) (pderiv i P)) •
            (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
        ((∑ j, (MvPolynomial.eval (fun k => x k) (pderiv j (pderiv i P))) •
            (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).smulRight
          (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) x :=
      fun i => (MvPolyFDerivEuclidean (pderiv i P) x).smul_const
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    have hfe : (∑ i, fun y : EuclideanSpace ℝ (Fin n) =>
          (MvPolynomial.eval (fun j => y j) (pderiv i P)) •
            (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
        = fun y : EuclideanSpace ℝ (Fin n) =>
          ∑ i, (MvPolynomial.eval (fun j => y j) (pderiv i P)) •
            (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
      funext y
      simp
    exact hfe ▸ HasFDerivAt.sum (fun i _ => hterm i)
  rw [iteratedFDeriv_two_apply, hfd, hG.fderiv]
  simp
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
