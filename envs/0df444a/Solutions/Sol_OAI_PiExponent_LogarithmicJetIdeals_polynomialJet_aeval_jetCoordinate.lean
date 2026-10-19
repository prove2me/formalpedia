-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.polynomialJet_aeval_jetCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:07:52.836803+00:00
-- url     : https://prove2.me/submissions/ae4ff54f-a6bf-428e-8a80-314d0294d95c

import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.Ring

open OAI.PiExponent.LogarithmicJetIdeals

theorem solution {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (Q : MvPolynomial (Fin (m + 1)) ℂ) :
    polynomialJet c T (MvPolynomial.aeval (jetCoordinate c T) Q) = Q := by
  let x : MvPolynomial (Fin (m + 1)) ℂ := MvPolynomial.X 0
  have hx : polynomialJet c T (x - 1) = x := by
    dsimp only [x]
    simp only [map_sub, map_one, polynomialJet, MvPolynomial.aeval_X,
      Fin.cases_zero]
    ring
  have hC : (polynomialJet c T).toRingHom.comp
      (MvPolynomial.C : ℂ →+* MvPolynomial (Fin (m + 1)) ℂ) =
      MvPolynomial.C := by
    apply RingHom.ext
    intro a
    exact (polynomialJet c T).commutes a
  have hlog (p : Polynomial ℂ) :
      polynomialJet c T (Polynomial.eval₂ MvPolynomial.C (x - 1) p) =
        Polynomial.eval₂ MvPolynomial.C x p := by
    change (polynomialJet c T).toRingHom
      (Polynomial.eval₂ MvPolynomial.C (x - 1) p) = _
    rw [Polynomial.hom_eval₂, hC]
    change Polynomial.eval₂ MvPolynomial.C (polynomialJet c T (x - 1)) p = _
    rw [hx]
  have hcoord : ∀ i : Fin (m + 1),
      polynomialJet c T (jetCoordinate c T i) = MvPolynomial.X i := by
    intro i
    cases i using Fin.cases with
    | zero =>
        change polynomialJet c T (x - 1) = x
        exact hx
    | succ i =>
        change polynomialJet c T
          (MvPolynomial.X i.succ - MvPolynomial.C (c i) -
            Polynomial.eval₂ MvPolynomial.C (x - 1)
              (OAI.PiExponent.InterpolationMatrix.truncatedLog (T i))) =
          MvPolynomial.X i.succ
        rw [map_sub, map_sub, hlog]
        simp only [polynomialJet, MvPolynomial.aeval_X, Fin.cases_succ,
          MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
        dsimp only [x]
        ring
  rw [MvPolynomial.comp_aeval_apply]
  have hfun : (fun i => polynomialJet c T (jetCoordinate c T i)) =
      (MvPolynomial.X : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ) :=
    funext hcoord
  rw [hfun]
  exact MvPolynomial.aeval_X_left_apply Q
