-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_coordinates_mem_realWeightedSimplex
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T21:01:50.468699+00:00
-- url     : https://prove2.me/submissions/afd227dc-0e5b-4a68-a3c9-5b372272d3f2

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {d : Nat} (v : Fin d → Real) (H : Real)
    (hv : ∀ i, 0 < v i) (a : Fin d → Nat)
    (ha : ∑ i, v i * (a i : Real) ≤ H) :
    a ∈ OAI.PiExponent.realWeightedSimplex v H := by
  classical
  rw [realWeightedSimplex, Finset.mem_filter]
  constructor
  · apply Fintype.mem_piFinset.2
    intro i
    rw [Finset.mem_range]
    apply Nat.lt_succ_of_le
    have hterm : v i * (a i : Real) ≤
        ∑ j : Fin d, v j * (a j : Real) :=
      Finset.single_le_sum
        (fun j hj => mul_nonneg (le_of_lt (hv j)) (Nat.cast_nonneg _))
        (Finset.mem_univ i)
    have hbound : v i * (a i : Real) ≤ H := hterm.trans ha
    have hratio : (a i : Real) ≤ H / v i :=
      (le_div_iff₀ (hv i)).2 (by simpa [mul_comm] using hbound)
    have hH : 0 ≤ H := (mul_nonneg (le_of_lt (hv i)) (Nat.cast_nonneg (a i))).trans hbound
    exact (Nat.le_floor_iff (div_nonneg hH (le_of_lt (hv i)))).2 hratio
  · exact ha