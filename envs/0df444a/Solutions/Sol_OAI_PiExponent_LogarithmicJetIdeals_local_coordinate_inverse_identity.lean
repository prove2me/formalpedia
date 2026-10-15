-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.local_coordinate_inverse_identity
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T20:44:51.625081+00:00
-- url     : https://prove2.me/submissions/5ee25933-7339-4b59-a8cd-9f972ecc706d

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Mathlib.Algebra.Polynomial.AlgebraMap

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPolynomial.aeval (jetCoordinate c T) (localCoordinatePolynomial c T P) = P := by
  let f : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ :=
    Fin.cases (1 + MvPolynomial.X 0)
      (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
        Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0)
          (InterpolationMatrix.truncatedLog (T i)))
  -- Substitution commutes with evaluating any univariate polynomial.
  have heval (Q : Polynomial ℂ) :
      MvPolynomial.aeval (jetCoordinate c T)
          (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) Q) =
        Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0 - 1) Q := by
    change MvPolynomial.aeval (jetCoordinate c T)
        (Polynomial.aeval (MvPolynomial.X 0) Q) =
      Polynomial.aeval (MvPolynomial.X 0 - 1) Q
    simpa only [MvPolynomial.aeval_X, jetCoordinate, Fin.cases_zero] using
      (Polynomial.aeval_algHom_apply (MvPolynomial.aeval (jetCoordinate c T))
        (MvPolynomial.X (0 : Fin (m + 1))) Q).symm
  -- Each coordinate in the composed substitution is the original variable.
  have hf : (fun i => MvPolynomial.aeval (jetCoordinate c T) (f i)) =
      (fun i : Fin (m + 1) => MvPolynomial.X i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [f, Fin.cases_zero, map_add, map_one, MvPolynomial.aeval_X,
        jetCoordinate]
      ring
    · simp only [f, Fin.cases_succ, map_add, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq, MvPolynomial.aeval_X]
      rw [heval]
      simp only [jetCoordinate, Fin.cases_succ]
      ring
  change MvPolynomial.aeval (jetCoordinate c T) (MvPolynomial.aeval f P) = P
  calc
    MvPolynomial.aeval (jetCoordinate c T) (MvPolynomial.aeval f P) =
        MvPolynomial.aeval (fun i => MvPolynomial.aeval (jetCoordinate c T) (f i)) P :=
      MvPolynomial.comp_aeval_apply f (MvPolynomial.aeval (jetCoordinate c T)) P
    _ = MvPolynomial.aeval (fun i => MvPolynomial.X i) P := by rw [hf]
    _ = P := MvPolynomial.aeval_X_left_apply P