-- Prove2me | solution 1 for Kyprianou.Ch03.timeReversalFiniteCylinderPreimagesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:18:06.956271+00:00
-- url     : https://prove2.me/submissions/7b15f019-51a1-4be0-91f5-7f4cc5eaf2f0

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch03_levyNoFixedTimeJumpV1
import Theorems.Thm_Kyprianou_Ch03_rawReversalFiniteCylinderV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t)
    (J : Finset {s : NNReal // s <= t})
    (B : {s : NNReal // s <= t} -> Set Real)
    (hB : ∀ i ∈ J, MeasurableSet (B i)) :
    P ((fun omega : Omega =>
      fun s : {s : NNReal // s <= t} =>
        (if (s : NNReal) = t then X 0 omega
         else Function.leftLim (fun r : NNReal => X r omega) (t - (s : NNReal))) -
           X t omega) ⁻¹' Set.pi (J : Set {s : NNReal // s <= t}) B) =
    P ((fun omega : Omega => fun s : {s : NNReal // s <= t} => -(X (s : NNReal) omega)) ⁻¹' Set.pi (J : Set {s : NNReal // s <= t}) B) := by
  classical
  have h (s : J) : ∀ᵐ ω ∂P,
      (if (s.1 : NNReal) = t then X 0 ω else
        Function.leftLim (fun r : NNReal => X r ω) (t - (s.1 : NNReal))) =
        X (t - (s.1 : NNReal)) ω := by
    by_cases hs : (s.1 : NNReal) = t
    · simp [hs]
    · have hu : 0 < t - (s.1 : NNReal) :=
        tsub_pos_of_lt (lt_of_le_of_ne s.1.property hs)
      simpa only [if_neg hs] using
        Kyprianou.Ch03.levyNoFixedTimeJumpV1 P X hX _ hu
  have hall := ae_all_iff.mpr h
  calc
    _ = P ((fun ω : Omega => fun s : {s : NNReal // s <= t} =>
        X (t - (s : NNReal)) ω - X t ω) ⁻¹'
          Set.pi (J : Set {s : NNReal // s <= t}) B) := by
      apply measure_congr
      filter_upwards [hall] with ω hω
      apply propext
      change (∀ s ∈ (J : Set _), _ ∈ B s) ↔ (∀ s ∈ (J : Set _), _ ∈ B s)
      constructor <;> intro hh s hs
      · simpa only [← hω ⟨s, hs⟩] using hh s hs
      · simpa only [hω ⟨s, hs⟩] using hh s hs
    _ = _ := Kyprianou.Ch03.rawReversalFiniteCylinderV1 P X hX t ht J B hB
