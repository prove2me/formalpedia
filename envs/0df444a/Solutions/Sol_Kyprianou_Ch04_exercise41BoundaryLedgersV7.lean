-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41BoundaryLedgersV7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:23:09.310999+00:00
-- url     : https://prove2.me/submissions/5db8f147-2bb5-494d-a762-bc0b7187e31e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41BoundaryPathLedgerV8
import Theorems.Thm_Kyprianou_Ch04_exercise41NoJumpFromZeroV6
import Theorems.Thm_Kyprianou_Ch04_exercise41PositiveDepartureV7
import Theorems.Thm_Kyprianou_Ch04_exercise41ContinuousArrivalV7
import Theorems.Thm_Kyprianou_Ch04_exercise42AvramPathDataV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (Xleft : NNReal → Ω → ℝ)
    (hLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => L.X s w) (nhdsWithin t (Iio t)) (nhds (Xleft t w))) :
    ∀ᵐ w ∂P, ∀ (hVisits : ∀ t : NNReal,
      Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ L.X s w = 0}) (t : NNReal),
      let a := fun x : ℝ => if 0 ≤ x then (1 : ℝ) else 0
      let b := fun x : ℝ => if 0 < x then (1 : ℝ) else 0
      let μ := (pathJumpMeasure L.X Xleft w).restrict
        (Set.prod (Ioc (0 : ℝ) (t : ℝ)) (Iio (0 : ℝ)))
      let Ja := fun z : ℝ × ℝ => a (Xleft z.1.toNNReal w + z.2) - a (Xleft z.1.toNNReal w)
      let Jb := fun z : ℝ × ℝ => b (Xleft z.1.toNNReal w + z.2) - b (Xleft z.1.toNNReal w)
      let A : ℝ := ∑ s ∈ (hVisits t).toFinset, if Xleft s w = 0 then 1 else 0
      let B : ℝ := (if 0 < t then 1 else 0) +
        ∑ s ∈ (hVisits t).toFinset, if s < t then 1 else 0
      Integrable Ja μ ∧ Integrable Jb μ ∧
      a (L.X t w) = a (L.X 0 w) + (∫ z, Ja z ∂μ) + A ∧
      b (L.X t w) = b (L.X 0 w) + (∫ z, Jb z ∂μ) + B := by
  filter_upwards [
    exercise42AvramPathDataV1 P F L hBV hd Xleft hLeft,
    exercise41NoJumpFromZeroV6 P F L hBV hd,
    exercise41PositiveDepartureV7 P F L hBV hd,
    exercise41ContinuousArrivalV7 P F L hBV hd
  ] with w hw hn hp ha
  obtain ⟨hCadlag,hL,hNeg,_,_,_⟩ := hw
  intro hVisits t
  exact exercise41BoundaryPathLedgerV8 L.X Xleft w L.drift hd
    (L.X_zero w) hCadlag hL hNeg hn hp ha hVisits t
