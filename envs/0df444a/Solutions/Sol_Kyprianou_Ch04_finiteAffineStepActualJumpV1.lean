-- Prove2me | solution 1 for Kyprianou.Ch04.finiteAffineStepActualJumpV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:31:38.90334+00:00
-- url     : https://prove2.me/submissions/9c5d3fe9-5024-4c3b-90fe-a0e0b412aaa3

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteAffineStepStrictLeftLimitV1
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- The actual jump of a finite affine path is its retained mark, and vanishes elsewhere. -/
theorem solution (S : Finset NNReal) (j : NNReal → ℝ) (d : ℝ)
    (T : NNReal) (Y L : NNReal → ℝ)
    (hY : ∀ u ≤ T, Y u = d * (u : ℝ) + ∑ r ∈ S, if r ≤ u then j r else 0)
    (hL : ∀ u, 0 < u → Tendsto Y (𝓝[<] u) (𝓝 (L u))) :
    ∀ u, 0 < u → u ≤ T → Y u - L u = if u ∈ S then j u else 0 := by
  classical
  intro u hu huT
  rw [hY u huT,Kyprianou.Ch04.finiteAffineStepStrictLeftLimitV1 S j d T Y L hY hL u hu huT]
  rw [add_sub_add_left_eq_sub,← Finset.sum_sub_distrib]
  have he (r : NNReal) :
      (if r ≤ u then j r else 0) - (if r < u then j r else 0) =
        if r = u then j r else 0 := by
    rcases lt_trichotomy r u with h|h|h
    · simp [h,h.le,h.ne]
    · subst r; simp
    · simp [not_le.mpr h,not_lt.mpr h.le,ne_of_gt h]
  simp_rw [he]
  rw [Finset.sum_ite_eq' S u j]
