-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weight_le_cutoff_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:05:29.496211+00:00
-- url     : https://prove2.me/submissions/90ce0a8c-e84e-479d-84be-9ad1d3dab1a1

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (n : Fin d → Nat) (hn : ∀ i, 0 < n i)
    (e : Fin d →₀ Nat) (he : ∀ i : Fin d, e i < n i) :
    Finsupp.weight w e ≤ ∑ i : Fin d, ((n i : ℚ) - 1) * w i := by
  classical
  have hcoord : ∀ i : Fin d, (e i : ℚ) ≤ (n i : ℚ) - 1 := by
    intro i
    have hnat : e i + 1 ≤ n i := Nat.succ_le_of_lt (he i)
    have hcast : (e i : ℚ) + 1 ≤ (n i : ℚ) := by
      exact_mod_cast hnat
    linarith
  rw [Finsupp.weight_eq_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hwi : 0 ≤ w i := by
    exact_mod_cast (le_of_lt (hw i))
  simpa only [nsmul_eq_mul] using mul_le_mul_of_nonneg_right (hcoord i) hwi