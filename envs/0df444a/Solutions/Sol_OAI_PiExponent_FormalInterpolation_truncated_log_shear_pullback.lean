-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_log_shear_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:51:17.199378+00:00
-- url     : https://prove2.me/submissions/3730e180-8f3b-4089-b82b-c89fed650edf

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_log_shear_pullback_coordinate

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (T : Fin m → Nat)
    (Q : MvPolynomial (Fin (m + 1)) Complex) :
    ∃ P : MvPolynomial (Fin (m + 1)) Complex, ∀ c : Fin m → Complex,
      truncatedPolynomialJet c T P =
        MvPolynomial.aeval
          (fun i : Fin (m + 1) =>
            MvPolynomial.C (Fin.cases (0 : Complex) c i) + MvPolynomial.X i) Q := by
  refine ⟨MvPolynomial.aeval
    (fun i : Fin (m + 1) =>
      Fin.cases (MvPolynomial.X 0 - 1)
        (fun j => MvPolynomial.X j.succ -
          Polynomial.aeval (MvPolynomial.X 0 - 1)
            (OAI.PiExponent.InterpolationMatrix.truncatedLog (T j))) i) Q, ?_⟩
  intro c
  exact OAI.PiExponent.FormalInterpolation.truncated_log_shear_pullback_coordinate c T Q