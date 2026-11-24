-- Prove2me | solution 1 for MvPolyFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T14:26:38.327562+00:00
-- url     : https://prove2.me/submissions/8a88f22a-a42f-40d5-b926-67d3d8413d49

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_MvPolyFDeriv

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial ContinuousLinearMap
theorem _root_.solution {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (fun v : Fin n → ℝ => MvPolynomial.eval v P)
      (∑ i, (MvPolynomial.eval x (pderiv i P)) •
        (proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using (hasFDerivAt_const a x)
  | add p q hp hq =>
      simp only [map_add]
      refine (hp.add hq).congr_fderiv ?_
      simp [Finset.sum_add_distrib, add_smul]
  | mul_X p i hp =>
      have hxi : HasFDerivAt (fun v : Fin n → ℝ => v i)
          (proj i : (Fin n → ℝ) →L[ℝ] ℝ) x :=
        (proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt
      simp only [map_mul, MvPolynomial.eval_X]
      refine (hp.mul hxi).congr_fderiv ?_
      ext w
      simp only [add_apply, smul_apply, proj_apply, sum_apply, pderiv_mul,
        pderiv_X, map_add, map_mul, MvPolynomial.eval_X, smul_eq_mul, add_mul]
      rw [Finset.sum_add_distrib]
      have h1 : ∑ j, (eval x) ((pderiv j) p) * x i * w j
          = x i * ∑ j, (eval x) ((pderiv j) p) * w j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      have h2 : ∑ j, (eval x) p * (eval x) ((pderiv j) (X i : MvPolynomial (Fin n) ℝ)) * w j
          = (eval x) p * w i := by
        rw [Finset.sum_eq_single i]
        · simp [pderiv_X]
        · intro j _ hj; simp [pderiv_X, Ne.symm hj]
        · intro h; simp at h
      simp only [pderiv_X] at h2
      rw [h1, h2]
      ring
