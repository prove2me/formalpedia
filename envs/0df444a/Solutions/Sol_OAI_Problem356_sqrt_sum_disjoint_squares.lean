-- Prove2me | solution 1 for OAI.Problem356.sqrt_sum_disjoint_squares
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:12:41.134424+00:00
-- url     : https://prove2.me/submissions/347eca93-efbd-437c-9624-5d4ba30a60bc

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

open OAI OAI.Problem356
universe uIndex uX
open MeasureTheory
open scoped BigOperators


theorem solution {ι : Type uIndex} {X : Type uX} (s : Finset ι)
    (a : ι → ℝ) (g : ι → X → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (x : X) :
    Real.sqrt (∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, Real.sqrt (a i) * g i x := by
  classical
  by_cases hx : ∃ i ∈ s, g i x ≠ 0
  · obtain ⟨i, hi, hgi⟩ := hx
    have hz : ∀ j ∈ s, j ≠ i → g j x = 0 := by
      intro j hj hji
      by_contra hne
      exact Set.disjoint_left.mp (hd j hj i hi hji) (Function.mem_support.mpr hne) (Function.mem_support.mpr hgi)
    rw [Finset.sum_eq_single_of_mem i hi (fun j hj hji => by rw [hz j hj hji]; ring),
      Finset.sum_eq_single_of_mem i hi (fun j hj hji => by rw [hz j hj hji]; ring)]
    rw [Real.sqrt_mul (ha i hi), Real.sqrt_sq (hg i hi x)]
  · push Not at hx
    rw [Finset.sum_eq_zero (fun j hj => by rw [hx j hj]; ring),
      Finset.sum_eq_zero (fun j hj => by rw [hx j hj]; ring)]
    simp

