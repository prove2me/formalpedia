-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.isWeightedHomogeneous_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:42:12.398372+00:00
-- url     : https://prove2.me/submissions/d33f21d8-2613-4f1a-928d-8f79f88894c7

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → Rat) (i : Fin d) (e : Nat) :
    MvPolynomial.IsWeightedHomogeneous (fun i => (w i : Real))
      ((MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ e)
      ((e : Real) * (w i : Real)) := by
  let W : Fin d → Real := fun j => (w j : Real)
  have hX : MvPolynomial.IsWeightedHomogeneous W
      (MvPolynomial.X i : MvPolynomial (Fin d) Complex) (w i : Real) :=
    @MvPolynomial.isWeightedHomogeneous_X Complex Real inferInstance (Fin d) inferInstance W i
  simpa [W, nsmul_eq_mul] using hX.pow e
