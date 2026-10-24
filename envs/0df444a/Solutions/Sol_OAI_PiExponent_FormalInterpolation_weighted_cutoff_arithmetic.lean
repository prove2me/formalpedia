-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_cutoff_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T11:58:02.810833+00:00
-- url     : https://prove2.me/submissions/ea66a9e5-3803-457f-961a-eeea01501ea7

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d m : Nat} (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (s D n : Nat) (hs : 0 < s)
    (hD : (D : Real) < (s : Real) * ((rho : Real) + eps))
    (u : Fin m →₀ Nat) (hcut : s * (∑ j, u j) < n)
    (a : Fin d →₀ Nat)
    (hweight : ∑ k, (w k : Real) * (a k : Real) ≤
      (∑ j, (u j : Real)) * (D : Real)) :
    ∑ k, (w k : Real) * (a k : Real) ≤
      (n : Real) * ((rho : Real) + eps) := by
  have hsR : (0 : Real) < (s : Real) := by
    exact_mod_cast hs
  have hR : (0 : Real) < (rho : Real) + eps := by
    by_contra hnot
    have hRnonpos : (rho : Real) + eps ≤ 0 := le_of_not_gt hnot
    have hprod : (s : Real) * ((rho : Real) + eps) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hsR) hRnonpos
    have hDnonneg : (0 : Real) ≤ (D : Real) := Nat.cast_nonneg D
    linarith
  have hU : (0 : Real) ≤ ∑ j, (u j : Real) := by
    apply Finset.sum_nonneg
    intro j hj
    exact Nat.cast_nonneg (u j)
  have hcutR : (s : Real) * (∑ j, (u j : Real)) < (n : Real) := by
    exact_mod_cast hcut
  calc
    ∑ k, (w k : Real) * (a k : Real) ≤
        (∑ j, (u j : Real)) * (D : Real) := hweight
    _ ≤ (∑ j, (u j : Real)) * ((s : Real) * ((rho : Real) + eps)) := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hD) hU
    _ = ((s : Real) * (∑ j, (u j : Real))) * ((rho : Real) + eps) := by
      ring
    _ ≤ (n : Real) * ((rho : Real) + eps) := by
      exact mul_le_mul_of_nonneg_right (le_of_lt hcutR) (le_of_lt hR)