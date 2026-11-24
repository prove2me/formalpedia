-- Prove2me | solution 1 for MvPolyFDerivEuclidean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:14:39.869805+00:00
-- url     : https://prove2.me/submissions/f729d66e-3343-47e7-b8ca-7d3b998d361b

module
public import Definitions.Def_PHarmonicPoly_MvPolyFDeriv
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyFDeriv


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n : ℕ} (Q : MvPolynomial (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => z i) Q)
      (∑ i, (MvPolynomial.eval (fun j => y j) (pderiv i Q)) •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) y := by
  have hcomp : (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => z i) Q)
      = (fun u : Fin n → ℝ => MvPolynomial.eval u Q) ∘
        (EuclideanSpace.equiv (Fin n) ℝ) := rfl
  rw [hcomp]
  refine (HasFDerivAt.comp y (MvPolyFDeriv Q (fun j => y j))
    (EuclideanSpace.equiv (Fin n) ℝ).hasFDerivAt).congr_fderiv ?_
  ext z
  simp
