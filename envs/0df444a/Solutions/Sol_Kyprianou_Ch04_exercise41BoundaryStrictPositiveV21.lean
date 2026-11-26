-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41BoundaryStrictPositiveV21
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:06:51.916215+00:00
-- url     : https://prove2.me/submissions/2d7ddcba-7c51-474f-a70f-d3bd963b4a7d

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
    Summable (fun s : Ioc (0 : NNReal) t => ‖b (X s w) - b (Xleft s w)‖) ∧
    b (X t w) = b (X 0 w) + (∑' s : Ioc (0 : NNReal) t, (b (X s w) - b (Xleft s w))) + B := by
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
  let Z := fun u : Ioc (0 : NNReal) t => z (X u w)
  obtain ⟨hz,hZ⟩ := exercise41VisitIndicatorTsumV19 (fun s => X s w) t
    (hVisits t) (fun s => X s w = 0) (fun _ _ h => h)
  have he : (fun u : Ioc (0 : NNReal) t => b (X u w) - b (Xleft u w)) =
      (fun u => D u - Z u) := by
    funext u
    have hu := hab (X u w)
    rw [ha u] at hu
    dsimp [D,Z]
    rw [hb u u.2.1]
    linarith
  obtain ⟨hsb,hB⟩ := exercise41FiniteCorrectionSeriesV19 D Z hs hz
  refine ⟨?_,?_⟩
  · change Summable (fun u : Ioc (0 : NNReal) t => ‖b (X u w) - b (Xleft u w)‖)
    have H := congrArg (fun g : Ioc (0 : NNReal) t → ℝ => fun u => ‖g u‖) he
    change (fun u : Ioc (0 : NNReal) t => ‖b (X u w) - b (Xleft u w)‖) =
      (fun u => ‖D u - Z u‖) at H
    rw [H]
    exact hsb
  · by_cases ht : 0 < t
    · have H := exercise41VisitEndpointV19 (fun s => X s w) t ht (hVisits t)
      change b (X t w) = b (X 0 w) + (∑' u : Ioc (0 : NNReal) t, (b (X u w) - b (Xleft u w))) + _
      rw [he,hB]
      change b (X t w) = b (X 0 w) + ((∑' u : Ioc (0 : NNReal) t, (f u - Function.leftLim f u)) -
        (∑' u : Ioc (0 : NNReal) t, Z u)) + _
      rw [← hSum,show (∑' u : Ioc (0 : NNReal) t, Z u) = _ from hZ,H,if_pos ht]
      have Ht := hab (X t w)
      rw [ha t] at Ht
      have h0 : b (X 0 w) = 0 := by simp [b,hzero]
      rw [h0]
      change b (X t w) = 0 + (f t - (_ + z (X t w))) + (1 + _)
      linarith
    · have ht0 : t = 0 := le_antisymm (le_of_not_gt ht) bot_le
      subst t
      simp [b,hzero]

