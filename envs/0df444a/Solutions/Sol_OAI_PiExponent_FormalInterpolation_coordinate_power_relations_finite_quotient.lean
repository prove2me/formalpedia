-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_power_relations_finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:11:13.997199+00:00
-- url     : https://prove2.me/submissions/c8b970fb-8417-49e9-86a8-934f3471e9f4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_monomial_quotient
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_power_relations_span_le
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_of_ideal_le

open scoped BigOperators

theorem solution
    (d m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hrels : ∀ i : Fin d, ∃ N : Nat, 0 < N ∧
      ∃ q : Fin m → MvPolynomial (Fin d) ℂ,
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N = ∑ j, q j * p j) :
    Module.Finite ℂ
      (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p)) := by
  let N : Fin d → Nat := fun i => Classical.choose (hrels i)
  have hN : ∀ i, 0 < N i := fun i => (Classical.choose_spec (hrels i)).1
  have hpower : ∀ i, ∃ q : Fin m → MvPolynomial (Fin d) ℂ,
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N i = ∑ j, q j * p j :=
    fun i => (Classical.choose_spec (hrels i)).2
  let J : Ideal (MvPolynomial (Fin d) ℂ) :=
    Ideal.span (Set.range (fun i : Fin d => (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N i))
  let I : Ideal (MvPolynomial (Fin d) ℂ) := Ideal.span (Set.range p)
  have hJI : J ≤ I :=
    OAI.PiExponent.FormalInterpolation.coordinate_power_relations_span_le d m p N hpower
  have hJ : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ J) :=
    OAI.PiExponent.FormalInterpolation.finite_monomial_quotient d N hN
  simpa [I] using
    (OAI.PiExponent.FormalInterpolation.finite_quotient_of_ideal_le d J I hJI hJ)