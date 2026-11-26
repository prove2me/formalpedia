-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41BoundarySeriesAlgebraV20
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:04:49.911684+00:00
-- url     : https://prove2.me/submissions/abfda8d7-8f8c-4266-bb2b-5ecac625119b

import Theorems.Thm_Kyprianou_Ch04_exercise41BoundaryNonnegativeV21
import Theorems.Thm_Kyprianou_Ch04_exercise41BoundaryStrictPositiveV21
import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type}
    (X Xleft : NNReal → Ω → ℝ) (w : Ω) (t : NNReal)
    (hzero : X 0 w = 0)
    (hVisits : ∀ t : NNReal, Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ X s w = 0})
    (hNoJump : ∀ s : NNReal, 0 < s → Xleft s w = 0 → X s w = 0)
    (f : NNReal → ℝ)
    (hf : ∀ s, f s = (if X s w < 0 then -1 else 0))
    (hl : ∀ s, 0 < s → Function.leftLim f s = (if 0 < Xleft s w then 0 else -1))
    (hs : Set.Finite (Function.support (fun u : Ioc (0 : NNReal) t => f u - Function.leftLim f u)))
    (hSum : f t = ∑' u : Ioc (0 : NNReal) t, (f u - Function.leftLim f u)) :
    let a := fun x : ℝ => if 0 ≤ x then (1 : ℝ) else 0
    let b := fun x : ℝ => if 0 < x then (1 : ℝ) else 0
    let A : ℝ := ∑ s ∈ (hVisits t).toFinset, if Xleft s w = 0 then 1 else 0
    let B : ℝ := (if 0 < t then 1 else 0) +
      ∑ s ∈ (hVisits t).toFinset, if s < t then 1 else 0
    Summable (fun s : Ioc (0 : NNReal) t => ‖a (X s w) - a (Xleft s w)‖) ∧
    Summable (fun s : Ioc (0 : NNReal) t => ‖b (X s w) - b (Xleft s w)‖) ∧
    a (X t w) = a (X 0 w) + (∑' s : Ioc (0 : NNReal) t, (a (X s w) - a (Xleft s w))) + A ∧
    b (X t w) = b (X 0 w) + (∑' s : Ioc (0 : NNReal) t, (b (X s w) - b (Xleft s w))) + B := by
  obtain ⟨ha,hA⟩ := exercise41BoundaryNonnegativeV21 X Xleft w t hzero hVisits hNoJump f hf hl hs hSum
  obtain ⟨hb,hB⟩ := exercise41BoundaryStrictPositiveV21 X Xleft w t hzero hVisits hNoJump f hf hl hs hSum
  exact ⟨ha,hb,hA,hB⟩

