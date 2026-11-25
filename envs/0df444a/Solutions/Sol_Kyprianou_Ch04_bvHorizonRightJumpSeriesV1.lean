-- Prove2me | solution 1 for Kyprianou.Ch04.bvHorizonRightJumpSeriesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:33:41.996219+00:00
-- url     : https://prove2.me/submissions/8a061bef-1f92-4db3-a4a3-cc4630d2889f

import Mathlib
open MeasureTheory Filter Set
set_option autoImplicit false

theorem solution
    (g : NNReal → ℝ) (u t : NNReal) (hu : u ≤ t) :
    (∑' s : Set.Ioc (0 : NNReal) u, g s) =
      ∑' s : Set.Ioc (0 : NNReal) t, if (s : NNReal) ≤ u then g s else 0 := by
  classical
  let G : NNReal → ℝ := fun s => if s ≤ u then g s else 0
  change (∑' s : Set.Ioc (0 : NNReal) u, g s) =
    ∑' s : Set.Ioc (0 : NNReal) t, G s
  rw [tsum_subtype (Set.Ioc (0 : NNReal) u) g,
    tsum_subtype (Set.Ioc (0 : NNReal) t) G]
  apply tsum_congr
  intro s
  by_cases hsu : s ≤ u
  · have hst := hsu.trans hu
    simp [G, Set.indicator_apply, Set.mem_Ioc, hsu, hst]
  · simp [G, Set.indicator_apply, Set.mem_Ioc, hsu]
