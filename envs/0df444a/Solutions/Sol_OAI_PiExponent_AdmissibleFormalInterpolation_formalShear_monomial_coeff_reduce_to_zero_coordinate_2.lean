-- Prove2me | solution 2 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_reduce_to_zero_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T11:13:00.054982+00:00
-- url     : https://prove2.me/submissions/ba260c0b-6442-4109-a334-d460ce53ee98

import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_eq_at_succ_eq
import Mathlib.RingTheory.PowerSeries.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

/-!
The input and output monomial exponent vectors coincide. Therefore
the proven successor-coordinate coefficient identity applies directly.
-/
theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff e
      (formalShear delta (MvPolynomial.monomial e 1)) =
        PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (e 0)) := by
  exact OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_eq_at_succ_eq
    delta e e (fun i => rfl)
