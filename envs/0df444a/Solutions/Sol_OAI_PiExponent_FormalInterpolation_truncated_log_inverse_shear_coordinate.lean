-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_log_inverse_shear_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:07:43.484231+00:00
-- url     : https://prove2.me/submissions/fb4a23f5-580f-4c0e-b4b5-dcec8efba580

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

theorem solution
    {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (i : Fin (m + 1)) :
    MvPolynomial.aeval
      (fun k : Fin (m + 1) =>
        Fin.cases (1 + MvPolynomial.X (0 : Fin (m + 1)))
          (fun j => MvPolynomial.C (c j) + MvPolynomial.X j.succ +
            Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))
              (OAI.PiExponent.InterpolationMatrix.truncatedLog (T j))) k)
      (Fin.cases
        (MvPolynomial.X (0 : Fin (m + 1)) -
          (1 : MvPolynomial (Fin (m + 1)) Complex))
        (fun j => MvPolynomial.X j.succ -
          Polynomial.aeval
            (MvPolynomial.X (0 : Fin (m + 1)) -
              (1 : MvPolynomial (Fin (m + 1)) Complex))
            (OAI.PiExponent.InterpolationMatrix.truncatedLog (T j))) i) =
    MvPolynomial.C (Fin.cases (0 : Complex) c i) + MvPolynomial.X i := by
  set φ := (MvPolynomial.aeval
      (fun k : Fin (m + 1) =>
        Fin.cases (1 + MvPolynomial.X (0 : Fin (m + 1)))
          (fun j => MvPolynomial.C (c j) + MvPolynomial.X j.succ +
            Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))
              (OAI.PiExponent.InterpolationMatrix.truncatedLog (T j))) k) :
      MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (m + 1)) ℂ) with hφ
  have h0 : φ (MvPolynomial.X 0 - 1) = MvPolynomial.X 0 := by
    rw [map_sub, map_one, hφ, MvPolynomial.aeval_X, Fin.cases_zero]; ring
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cases_zero]
    rw [h0, map_zero, zero_add]
  · simp only [Fin.cases_succ]
    rw [map_sub, ← Polynomial.aeval_algHom_apply, h0, hφ, MvPolynomial.aeval_X, Fin.cases_succ]
    ring
