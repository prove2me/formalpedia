-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weightedHomogeneousComponent_mul_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:40:29.084405+00:00
-- url     : https://prove2.me/submissions/fdd48d84-35f1-4e0e-aa53-83e646e8a4f4

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (E : ℚ)
    (a : MvPolynomial (Fin d) Complex) (v : Fin d →₀ ℕ) (c : Complex) :
    MvPolynomial.weightedHomogeneousComponent w E
        (a * MvPolynomial.monomial v c) =
      MvPolynomial.weightedHomogeneousComponent w
          (E - Finsupp.weight w v) a * MvPolynomial.monomial v c := by
  classical
  ext m
  simp only [MvPolynomial.coeff_weightedHomogeneousComponent,
    MvPolynomial.coeff_mul_monomial']
  by_cases hv : v ≤ m
  · have hsum : Finsupp.weight w (m - v) + Finsupp.weight w v =
        Finsupp.weight w m := by
      calc
        Finsupp.weight w (m - v) + Finsupp.weight w v =
            Finsupp.weight w ((m - v) + v) := (map_add (Finsupp.weight w) _ _).symm
        _ = Finsupp.weight w m := by rw [tsub_add_cancel_of_le hv]
    have hweight : Finsupp.weight w (m - v) =
        Finsupp.weight w m - Finsupp.weight w v :=
      (eq_sub_iff_add_eq).2 hsum
    have htest : (Finsupp.weight w m = E) ↔
        (Finsupp.weight w (m - v) = E - Finsupp.weight w v) := by
      rw [hweight]
      constructor
      · intro hm
        simpa [hm]
      · intro hsub
        have hplus := congrArg (fun x : ℚ => x + Finsupp.weight w v) hsub
        simpa using hplus
    simp [hv, htest]
  · simp [hv]