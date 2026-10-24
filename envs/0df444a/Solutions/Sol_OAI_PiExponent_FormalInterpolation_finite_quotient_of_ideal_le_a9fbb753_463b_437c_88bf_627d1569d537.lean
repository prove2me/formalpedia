-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_of_ideal_le_a9fbb753_463b_437c_88bf_627d1569d537
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:02:21.480983+00:00
-- url     : https://prove2.me/submissions/ab609673-ae9d-437e-a10c-7c10fefa31c2

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution {d : Nat} (J I : Ideal (MvPolynomial (Fin d) ℂ)) (hJI : J ≤ I)
    (hfin : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ J)) :
    Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ I) := by
  letI : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ J) := hfin
  let f : (MvPolynomial (Fin d) ℂ ⧸ J) →ₐ[ℂ]
      (MvPolynomial (Fin d) ℂ ⧸ I) :=
    Ideal.Quotient.factorₐ ℂ hJI
  apply Module.Finite.of_surjective f.toLinearMap
  change Function.Surjective (Ideal.Quotient.factor hJI)
  exact Ideal.Quotient.factor_surjective hJI