-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.X_pow_weightedHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:13:20.586737+00:00
-- url     : https://prove2.me/submissions/567be524-6254-494c-a297-21f28ebb3541

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

theorem solution
    {d : Nat} (w : Fin d → Rat) (i : Fin d) (n : Nat) :
    ((MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ n).IsWeightedHomogeneous
      (fun l => (w l : Real)) ((n : Real) * (w i : Real)) := by
  simpa [nsmul_eq_mul] using
    (MvPolynomial.IsWeightedHomogeneous.pow
      (MvPolynomial.isWeightedHomogeneous_X (R := Complex) (fun l => (w l : Real)) i) n)