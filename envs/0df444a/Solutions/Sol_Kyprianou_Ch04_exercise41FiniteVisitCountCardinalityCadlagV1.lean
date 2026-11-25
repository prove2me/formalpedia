-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FiniteVisitCountCardinalityCadlagV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:53:33.683808+00:00
-- url     : https://prove2.me/submissions/57a9295b-a403-43be-bfce-4c939f3d5113

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41FiniteMarkCountCadlagV1
open Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem solution (S : Finset NNReal) :
    (∀ t : NNReal, ContinuousWithinAt
      (fun u : NNReal => ((S.filter (fun s => s ≤ u)).card : ℝ))
      (Ici t) t) ∧
    (∀ t : NNReal, 0 < t → ∃ l : ℝ, Tendsto
      (fun u : NNReal => ((S.filter (fun s => s ≤ u)).card : ℝ))
      (nhdsWithin t (Iio t)) (nhds l)) := by
  classical
  have heq : (fun u : NNReal => ((S.filter (fun s => s ≤ u)).card : ℝ)) =
      (fun u : NNReal => ∑ s ∈ S, if s ≤ u then (1 : ℝ) else 0) := by
    funext u
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    simp
  simpa only [heq] using
    (Kyprianou.Ch04.exercise41FiniteMarkCountCadlagV1 S)
