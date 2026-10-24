-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_of_ideal_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:22:20.633983+00:00
-- url     : https://prove2.me/submissions/dfb97b06-b9ca-41bc-b48c-e2ba9f2390fe

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.LinearAlgebra.Quotient.Basic

open scoped BigOperators

theorem solution (d : Nat) (J I : Ideal (MvPolynomial (Fin d) ℂ))
    (hJI : J ≤ I)
    (hJ : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ J)) :
    Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ I) := by
  let hsub : J.restrictScalars ℂ ≤ I.restrictScalars ℂ := hJI
  let f : (MvPolynomial (Fin d) ℂ ⧸ J) →ₗ[ℂ]
      (MvPolynomial (Fin d) ℂ ⧸ I) :=
    Submodule.factor hsub
  have hf : Function.Surjective f :=
    Submodule.factor_surjective hsub
  letI : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ J) := hJ
  exact Module.Finite.of_surjective f hf