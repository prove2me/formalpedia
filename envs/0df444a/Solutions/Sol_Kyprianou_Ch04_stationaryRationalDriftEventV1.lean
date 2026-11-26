-- Prove2me | solution 1 for Kyprianou.Ch04.stationaryRationalDriftEventV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:44:31.710684+00:00
-- url     : https://prove2.me/submissions/500e5736-889f-4bce-be54-8241c3ee25ca

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_shiftedIsLevyProcessV1
import Theorems.Thm_Kyprianou_Ch02_levyWholePathLawEqOfMarginalLawsV1
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Stationarity transfers the rational-time small-time drift event to the origin. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P)
    (d : ℝ) (s : ℝ≥0) :
    (∀ᵐ ω ∂P, Tendsto
      (fun r : ℚ => (X (s + Real.toNNReal (r : ℝ)) ω - X s ω) /
        (Real.toNNReal (r : ℝ) : ℝ))
      (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds d)) ↔
    (∀ᵐ ω ∂P, Tendsto
      (fun r : ℚ => X (Real.toNNReal (r : ℝ)) ω /
        (Real.toNNReal (r : ℝ) : ℝ))
      (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds d)) := by
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => X (s + t) ω - X s ω
  have hY := Kyprianou.Ch04.shiftedIsLevyProcessV1 P X hX s
  have hLaw (t : ℝ≥0) : P.map (Y t) = P.map (X t) := by
    have h := (hX.stationary_increments s t).map_eq
    change P.map (fun ω => X (s + t) ω - X s ω) = P.map (fun ω => X t ω - X 0 ω) at h
    simpa only [hX.start_zero, sub_zero] using h
  have hEq := Kyprianou.Ch02.levyWholePathLawEqOfMarginalLawsV1 P P Y X hY hX hLaw
  let A : (ℝ≥0 → ℝ) → Prop := fun x =>
    Tendsto (fun r : ℚ => x (Real.toNNReal (r : ℝ)) / (Real.toNNReal (r : ℝ) : ℝ))
      (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds d)
  have hAm : MeasurableSet {x | A x} := by
    apply measurableSet_tendsto (nhds d)
    intro r
    exact (measurable_pi_apply _).div_const _
  have hYm := Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P Y hY
  have hXm := Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P X hX
  change (∀ᵐ ω ∂P, A (fun t => Y t ω)) ↔ (∀ᵐ ω ∂P, A (fun t => X t ω))
  rw [← ae_map_iff hYm hAm, hEq, ae_map_iff hXm hAm]
