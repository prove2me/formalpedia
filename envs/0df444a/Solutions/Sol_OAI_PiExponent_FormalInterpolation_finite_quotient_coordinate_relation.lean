-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_coordinate_relation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:47:17.846347+00:00
-- url     : https://prove2.me/submissions/f9e14b81-64bb-4eac-ba91-052bd377c1e6

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Algebraic.Integral

theorem solution
    {d : Nat} (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hquot : Module.Finite ℂ
      (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p)))
    (i : Fin d) :
    ∃ q : Polynomial ℂ, q ≠ 0 ∧
      Polynomial.aeval (MvPolynomial.X i) q ∈ Ideal.span (Set.range p) := by
  let I : Ideal (MvPolynomial (Fin d) ℂ) := Ideal.span (Set.range p)
  let A := MvPolynomial (Fin d) ℂ ⧸ I
  letI : Module.Finite ℂ A := hquot
  let x : A := Ideal.Quotient.mk I (MvPolynomial.X i)
  obtain ⟨q, hq, hqx⟩ := IsAlgebraic.of_finite (R := ℂ) x
  refine ⟨q, hq, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change Ideal.Quotient.mk I (Polynomial.aeval (MvPolynomial.X i) q) = 0
  have hcomp :
      (algebraMap ℂ A).comp (RingHom.id ℂ) =
        (Ideal.Quotient.mk I).comp
          (algebraMap ℂ (MvPolynomial (Fin d) ℂ)) := by
    ext z
    change algebraMap ℂ A z =
      Ideal.Quotient.mk I (algebraMap ℂ (MvPolynomial (Fin d) ℂ) z)
    exact (Ideal.Quotient.mk_algebraMap (R₁ := ℂ) I z).symm
  have hmap :=
    Polynomial.map_aeval_eq_aeval_map hcomp q (MvPolynomial.X i)
  rw [hmap]
  simpa [x] using hqx