-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_representatives_of_coordinate_relations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:36:41.705174+00:00
-- url     : https://prove2.me/submissions/b2d31f4c-f233-446c-87b8-f420570b3ca2

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_coordinate_power_representative
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_product_representative

open scoped BigOperators

theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (N : Nat)
    (hN : 0 < N)
    (hrel : ∀ i : Fin (m + 1), ∃ c : Fin N → Complex,
      MvPolynomial.X i ^ N -
        ∑ k : Fin N, MvPolynomial.C (c k) * MvPolynomial.X i ^ k.val ∈ J) :
    ∀ a : Fin (m + 1) →₀ Nat,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧
          MvPolynomial.monomial a (1 : Complex) - R ∈ J := by
  intro a
  apply OAI.PiExponent.FormalInterpolation.bounded_product_representative
  intro i
  obtain ⟨c, hc⟩ := hrel i
  exact OAI.PiExponent.FormalInterpolation.bounded_coordinate_power_representative
    (J := J) (N := N) (hN := hN) (i := i) (n := a i) (c := c) hc