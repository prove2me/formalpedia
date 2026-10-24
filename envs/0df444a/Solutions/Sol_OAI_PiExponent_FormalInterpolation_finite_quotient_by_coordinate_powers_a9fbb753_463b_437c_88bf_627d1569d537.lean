-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_by_coordinate_powers_a9fbb753_463b_437c_88bf_627d1569d537
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:06:44.673985+00:00
-- url     : https://prove2.me/submissions/38233c1c-b0ce-48b8-9d79-34b4232f7ba1

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_of_coordinate_powers_aux_a9fbb753_463b_437c_88bf_627d1569d537

open scoped BigOperators

theorem solution {d : Nat} (N : Nat) :
    Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸
      Ideal.span (Set.range (fun i : Fin d =>
        MvPolynomial.monomial (Finsupp.single i N) (1 : ℂ)))) := by
  let J : Ideal (MvPolynomial (Fin d) ℂ) :=
    Ideal.span (Set.range (fun i : Fin d =>
      MvPolynomial.monomial (Finsupp.single i N) (1 : ℂ)))
  apply OAI.PiExponent.FormalInterpolation.finite_quotient_of_coordinate_powers_aux_a9fbb753_463b_437c_88bf_627d1569d537 J
  intro i
  refine ⟨Nat.succ N, Nat.zero_lt_succ _, ?_⟩
  have hgen : MvPolynomial.monomial (Finsupp.single i N) (1 : ℂ) ∈ J :=
    Ideal.subset_span (Set.mem_range_self i)
  have hpow : (MvPolynomial.X i) ^ N ∈ J := by
    rw [MvPolynomial.X_pow_eq_monomial]
    exact hgen
  simpa [pow_succ, mul_comm] using J.mul_mem_left (MvPolynomial.X i) hpow