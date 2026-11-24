-- Prove2me | solution 1 for MvPolyGradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:14:04.48254+00:00
-- url     : https://prove2.me/submissions/aede09fa-4963-4711-836e-7e03d8626604

module
public import Definitions.Def_PHarmonicPoly_MvPolyFDeriv
public import Definitions.Def_PHarmonicPoly_MvPolyGradient
public import Theorems.Thm_MvPolyFDeriv


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial ContinuousLinearMap InnerProductSpace
theorem _root_.solution {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x
      = WithLp.toLp 2 (fun i => MvPolynomial.eval (fun j => x j) (pderiv i P)) := by
  have hcomp : (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
      = (fun v : Fin n → ℝ => MvPolynomial.eval v P) ∘ (EuclideanSpace.equiv (Fin n) ℝ) := rfl
  have hF : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
      ((∑ i, (MvPolynomial.eval (fun j => x j) (pderiv i P)) •
          (proj i : (Fin n → ℝ) →L[ℝ] ℝ)).comp
        (EuclideanSpace.equiv (Fin n) ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ))) x := by
    rw [hcomp]
    exact HasFDerivAt.comp x (MvPolyFDeriv P (fun j => x j))
      (EuclideanSpace.equiv (Fin n) ℝ).hasFDerivAt
  refine HasGradientAt.gradient ?_
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hF.congr_fderiv ?_
  ext w
  rw [toDual_apply_apply, PiLp.inner_apply]
  simp [mul_comm]
