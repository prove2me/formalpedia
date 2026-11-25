-- Prove2me | solution 1 for Kyprianou.Ch04.bvHorizonJumpSeriesReindexV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:04:49.759259+00:00
-- url     : https://prove2.me/submissions/14e24188-9fab-4bc5-8282-d21aab922664

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega)
    (f : ℝ × ℝ → ℝ) (t : NNReal) :
    (∑' s : {s : NNReal | 0 < s ∧ X s omega ≠ Xleft s omega},
      (Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ)).indicator
        (fun z => f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
          f (z.1, Xleft (Real.toNNReal z.1) omega))
        (((s : NNReal) : ℝ), X s omega - Xleft s omega)) =
      ∑' s : Set.Ioc (0 : NNReal) t,
        (f (((s : NNReal) : ℝ), X s omega) - f (((s : NNReal) : ℝ), Xleft s omega)) := by
  classical
  let J : Set NNReal := {s | 0 < s ∧ X s omega ≠ Xleft s omega}
  let B : Set (ℝ × ℝ) := Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) Set.univ
  let F : NNReal → ℝ := fun s =>
    B.indicator (fun z => f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
      f (z.1, Xleft (Real.toNNReal z.1) omega))
      ((s : ℝ), X s omega - Xleft s omega)
  let G : NNReal → ℝ := fun s => f ((s : ℝ), X s omega) - f ((s : ℝ), Xleft s omega)
  change (∑' s : J, F s) = ∑' s : Set.Ioc (0 : NNReal) t, G s
  rw [tsum_subtype J F, tsum_subtype (Set.Ioc (0 : NNReal) t) G]
  apply tsum_congr
  intro s
  have hv : Xleft s omega + (X s omega - Xleft s omega) = X s omega := by ring
  by_cases hj : X s omega = Xleft s omega
  · simp [J, F, G, B, Set.indicator_apply, hj]
  · by_cases hp : 0 < s
    · have hm : ((s : ℝ), X s omega - Xleft s omega) ∈ B ↔ s ≤ t := by
        change ((0 : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) ≤ (t : ℝ)) ∧
          X s omega - Xleft s omega ∈ (Set.univ : Set ℝ) ↔ s ≤ t
        simp
      simp [J, F, G, Set.indicator_apply, hj, hp, hv, hm]
    · simp [J, F, G, B, Set.indicator_apply, hp]
