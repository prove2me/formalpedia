-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_of_coordinate_powers_general
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:56:00.199405+00:00
-- url     : https://prove2.me/submissions/111ee7db-3294-474d-8582-0d6482d119df

import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_by_coordinate_powers
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_descend

universe u

open OAI.PiExponent.FormalInterpolation

theorem solution
    {R : Type u} [CommRing R] {d : Nat}
    (J : Ideal (MvPolynomial (Fin d) R))
    (hpow : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧ MvPolynomial.X i ^ e ∈ J) :
    Module.Finite R ((MvPolynomial (Fin d) R) ⧸ J) := by
  classical
  let e : Fin d → Nat := fun i => Classical.choose (hpow i)
  have he : ∀ i : Fin d, 0 < e i := by
    intro i
    exact (Classical.choose_spec (hpow i)).1
  have hp : ∀ i : Fin d, MvPolynomial.X i ^ e i ∈ J := by
    intro i
    exact (Classical.choose_spec (hpow i)).2
  let K : Ideal (MvPolynomial (Fin d) R) :=
    Ideal.span (Set.range fun i : Fin d => MvPolynomial.X i ^ e i)
  have hK : K ≤ J := by
    apply Ideal.span_le.2
    rintro p ⟨i, rfl⟩
    exact hp i
  have hfinite : Module.Finite R ((MvPolynomial (Fin d) R) ⧸ K) :=
    OAI.PiExponent.FormalInterpolation.finite_quotient_by_coordinate_powers (R := R) e he
  exact OAI.PiExponent.FormalInterpolation.finite_quotient_descend (R := R) (A := MvPolynomial (Fin d) R) K J hK hfinite