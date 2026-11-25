-- Prove2me | solution 1 for GradientEuler
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:36:17.098097+00:00
-- url     : https://prove2.me/submissions/efe6deb6-792e-434d-956c-96c803cadde9

module
public import Definitions.Def_PHarmonicPoly_MvPolyHessian
public import Definitions.Def_PHarmonicPoly_MvPolyGradientInner
public import Definitions.Def_PHarmonicPoly_GradientEuler
public import Theorems.Thm_MvPolyGradientInner
public import Theorems.Thm_MvPolyHessian


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n m : ℕ} (hm : 1 ≤ m) {P : MvPolynomial (Fin n) ℝ}
    (hhom : P.IsHomogeneous m) (x w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) =>
          MvPolynomial.eval (fun i => y i) P) x) x
        = (m : ℝ) * MvPolynomial.eval (fun i => x i) P
      ∧ iteratedFDeriv ℝ 2
          (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x ![x, w]
        = ((m : ℝ) - 1) * inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => y i) P) x) w := by
  have heuler : ∀ (Q : MvPolynomial (Fin n) ℝ) (d : ℕ), Q.IsHomogeneous d →
      ∑ i, (x i) * MvPolynomial.eval (fun j => x j) (pderiv i Q)
        = (d : ℝ) * MvPolynomial.eval (fun j => x j) Q := by
    intro Q d hQ
    have h2 := congrArg (MvPolynomial.eval (fun j => x j)) hQ.sum_X_mul_pderiv
    simpa [nsmul_eq_mul] using h2
  refine ⟨?_, ?_⟩
  · rw [(MvPolyGradientInner P x x).1, ← heuler P m hhom]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  · have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have : (1 : ℕ) ≤ m := hm
      push_cast [Nat.cast_sub this]
      ring
    rw [MvPolyHessian P x x w, (MvPolyGradientInner P x w).1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : (pderiv j P).IsHomogeneous (m - 1) := hhom.pderiv
    have hE := heuler (pderiv j P) (m - 1) hj
    calc ∑ i, x i * w j * MvPolynomial.eval (fun k => x k) (pderiv i (pderiv j P))
        = w j * ∑ i, x i * MvPolynomial.eval (fun k => x k) (pderiv i (pderiv j P)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = w j * (((m - 1 : ℕ) : ℝ) * MvPolynomial.eval (fun k => x k) (pderiv j P)) := by
          rw [hE]
      _ = ((m : ℝ) - 1) * (MvPolynomial.eval (fun k => x k) (pderiv j P) * w j) := by
          rw [hcast]; ring
