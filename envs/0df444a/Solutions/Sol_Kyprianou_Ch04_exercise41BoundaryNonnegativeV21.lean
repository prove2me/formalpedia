-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41BoundaryNonnegativeV21
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:08:22.95118+00:00
-- url     : https://prove2.me/submissions/e6c16134-89ec-46ed-a71e-bd1190ab3154

import Theorems.Thm_Kyprianou_Ch04_exercise41VisitIndicatorTsumV19
import Theorems.Thm_Kyprianou_Ch04_exercise41FiniteCorrectionSeriesV19
import Theorems.Thm_Kyprianou_Ch04_exercise41VisitEndpointV19
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
    a (X t w) = a (X 0 w) + (∑' s : Ioc (0 : NNReal) t, (a (X s w) - a (Xleft s w))) + A := by
  classical
  dsimp only
  let a := fun x : ℝ => if 0 ≤ x then (1 : ℝ) else 0
  let b := fun x : ℝ => if 0 < x then (1 : ℝ) else 0
  let z := fun x : ℝ => if x = 0 then (1 : ℝ) else 0
  have hab (x : ℝ) : a x = b x + z x := by
    rcases lt_trichotomy x 0 with h | h | h
    · simp [a,b,z,not_le_of_gt h,not_lt_of_ge h.le,h.ne]
    · simp [a,b,z,h]
    · simp [a,b,z,h,h.le,h.ne.symm]
  have ha (s : NNReal) : a (X s w) = f s + 1 := by
    rw [hf]
    by_cases h : X s w < 0 <;> simp [a,h,not_le_of_gt,le_of_not_gt]
  have hb (s : NNReal) (hp : 0 < s) : b (Xleft s w) = Function.leftLim f s + 1 := by
    rw [hl s hp]
    by_cases h : 0 < Xleft s w <;> simp [b,h]
  let D := fun u : Ioc (0 : NNReal) t => f u - Function.leftLim f u
  let Z := fun u : Ioc (0 : NNReal) t => z (Xleft u w)
  obtain ⟨hz,hZ⟩ := exercise41VisitIndicatorTsumV19 (fun s => X s w) t
    (hVisits t) (fun s => Xleft s w = 0) hNoJump
  have he : (fun u : Ioc (0 : NNReal) t => a (X u w) - a (Xleft u w)) =
      (fun u => D u - Z u) := by
    funext u
    dsimp [D,Z]
    rw [ha,hab (Xleft u w),hb u u.2.1]
    ring
  obtain ⟨hsa,hA⟩ := exercise41FiniteCorrectionSeriesV19 D Z hs hz
  refine ⟨?_,?_⟩
  · change Summable (fun u : Ioc (0 : NNReal) t => ‖a (X u w) - a (Xleft u w)‖)
    have H := congrArg (fun g : Ioc (0 : NNReal) t → ℝ => fun u => ‖g u‖) he
    change (fun u : Ioc (0 : NNReal) t => ‖a (X u w) - a (Xleft u w)‖) =
      (fun u => ‖D u - Z u‖) at H
    rw [H]
    exact hsa
  · change a (X t w) = a (X 0 w) + (∑' u : Ioc (0 : NNReal) t, (a (X u w) - a (Xleft u w))) + _
    rw [he,hA]
    change a (X t w) = a (X 0 w) + ((∑' u : Ioc (0 : NNReal) t, (f u - Function.leftLim f u)) -
      (∑' u : Ioc (0 : NNReal) t, Z u)) + _
    rw [← hSum,show (∑' u : Ioc (0 : NNReal) t, Z u) = _ from hZ,ha t]
    have h0 : a (X 0 w) = 1 := by simp [a,hzero]
    rw [h0]
    ring

