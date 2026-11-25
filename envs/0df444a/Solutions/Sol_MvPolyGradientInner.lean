-- Prove2me | solution 1 for MvPolyGradientInner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:24:39.461748+00:00
-- url     : https://prove2.me/submissions/fe715b87-850e-4770-8394-088bcb96c042

module
public import Definitions.Def_PHarmonicPoly_MvPolyGradient
public import Definitions.Def_PHarmonicPoly_MvPolyGradientInner
public import Theorems.Thm_MvPolyGradient


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (y z : EuclideanSpace ℝ (Fin n)) :
    (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
          MvPolynomial.eval (fun i => q i) P) y) z : ℝ)
        = ∑ i, MvPolynomial.eval (fun j => y j) (pderiv i P) * z i
      ∧ (∑ i, (MvPolynomial.eval (fun j => y j) (pderiv i P)) •
          (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) z
        = (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => q i) P) y) z : ℝ) := by
  have h1 : (inner ℝ (gradient (fun q : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun i => q i) P) y) z : ℝ)
      = ∑ i, MvPolynomial.eval (fun j => y j) (pderiv i P) * z i := by
    rw [MvPolyGradient P y, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  refine ⟨h1, ?_⟩
  rw [h1]
  simp
