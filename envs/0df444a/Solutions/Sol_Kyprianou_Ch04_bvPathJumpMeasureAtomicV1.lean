-- Prove2me | solution 1 for Kyprianou.Ch04.bvPathJumpMeasureAtomicV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:53:10.068859+00:00
-- url     : https://prove2.me/submissions/e362640a-c8bf-419b-8808-4361e699d204

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
    (hJ : ({s : NNReal | 0 < s ∧ X s omega ≠ Xleft s omega}).Countable) :
    pathJumpMeasure X Xleft omega =
      Measure.sum (fun s : {s : NNReal | 0 < s ∧ X s omega ≠ Xleft s omega} => Measure.dirac
        (((s : NNReal) : ℝ), X s omega - Xleft s omega)) := by
  classical
  let J : Set NNReal := {s : NNReal | 0 < s ∧ X s omega ≠ Xleft s omega}
  change J.Countable at hJ
  letI : Countable J := hJ.to_subtype
  let φ : NNReal → ℝ × ℝ := fun s => ((s : ℝ), X s omega - Xleft s omega)
  have hφ : AEMeasurable φ ((Measure.count : Measure NNReal).restrict J) :=
    aemeasurable_restrict_of_measurable_subtype hJ.measurableSet (measurable_of_countable _)
  change Measure.map φ ((Measure.count : Measure NNReal).restrict J) = _
  ext U hU
  rw [Measure.map_apply_of_aemeasurable hφ hU, Measure.restrict_apply' hJ.measurableSet]
  have hV : MeasurableSet (φ ⁻¹' U ∩ J) := (hJ.mono Set.inter_subset_right).measurableSet
  rw [Measure.count, Measure.sum_apply _ hV, Measure.sum_apply _ hU,
    tsum_subtype J (fun s => (Measure.dirac (φ s)) U)]
  apply tsum_congr
  intro s
  by_cases hs : s ∈ J <;> by_cases hu : φ s ∈ U <;>
    simp [Measure.dirac_apply, Set.indicator_apply, hs, hu]
