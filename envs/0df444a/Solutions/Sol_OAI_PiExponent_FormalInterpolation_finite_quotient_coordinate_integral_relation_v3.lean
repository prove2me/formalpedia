-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_coordinate_integral_relation_v3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:52:39.333292+00:00
-- url     : https://prove2.me/submissions/6611436a-80fd-42c0-a357-b6cd74d300a0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) ℂ))
    (hquot : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ I))
    (i : Fin d) :
    ∃ p : Polynomial ℂ, p ≠ 0 ∧
      Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) p ∈ I := by
  let A := MvPolynomial (Fin d) ℂ ⧸ I
  letI := hquot
  let x : A := Ideal.Quotient.mk I (MvPolynomial.X i)
  have hx : IsIntegral ℂ x := IsIntegral.of_finite ℂ x
  obtain ⟨p, hp, hroot⟩ := hx
  refine ⟨p, hp.ne_zero, ?_⟩
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  have hcomp : (Ideal.Quotient.mk I).comp MvPolynomial.C = algebraMap ℂ A := by
    change (Ideal.Quotient.mk I).comp
        (algebraMap ℂ (MvPolynomial (Fin d) ℂ)) =
      algebraMap ℂ ((MvPolynomial (Fin d) ℂ) ⧸ I)
    exact Ideal.Quotient.mk_comp_algebraMap ℂ I
  have hmap := Polynomial.hom_eval₂ p MvPolynomial.C
    (Ideal.Quotient.mk I) (MvPolynomial.X i)
  calc
    (Ideal.Quotient.mk I)
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) p) =
        Polynomial.eval₂ ((Ideal.Quotient.mk I).comp MvPolynomial.C)
          (Ideal.Quotient.mk I (MvPolynomial.X i)) p := hmap
    _ = Polynomial.eval₂ (algebraMap ℂ A) x p := by rw [hcomp]
    _ = 0 := hroot