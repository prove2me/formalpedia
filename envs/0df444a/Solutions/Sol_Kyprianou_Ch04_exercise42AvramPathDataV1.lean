-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42AvramPathDataV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:00:44.152066+00:00
-- url     : https://prove2.me/submissions/7cbe58c4-c7b8-45d6-b7e5-80dbeb1e4789

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42AvramLevyTripletBridgeV1
import Theorems.Thm_Kyprianou_Ch04_bvActualJumpDriftRepresentationV1
import Theorems.Thm_Kyprianou_Ch04_exercise42PositiveSupremumV1
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open ProbabilityTheory Set Topology
open scoped Topology
open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      ∀ t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => L.X s omega)
          (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega))) :
    ∀ᵐ omega : Omega ∂P,
      IsCadlag (fun t : NNReal => L.X t omega) ∧
      (∀ t : NNReal, 0 < t →
        Tendsto (fun s : NNReal => L.X s omega)
          (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega))) ∧
      (∀ t : NNReal, 0 < t → L.X t omega ≤ Xleft t omega) ∧
      (∀ t : NNReal,
        Summable (fun s : Set.Ioc (0 : NNReal) t => |L.X s omega - Xleft s omega|) ∧
        L.X t omega = L.X 0 omega + L.drift * (t : Real) +
          ∑' s : Set.Ioc (0 : NNReal) t, (L.X s omega - Xleft s omega)) ∧
      (∀ t : NNReal, 0 < t →
        0 < sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)) ∧
      Monotone (fun t : NNReal => (t : Real) * L.drift - L.X t omega) := by
  letI : IsProbabilityMeasure P := L.isProbability
  obtain ⟨hLevy, triplet, hTriplet, hTripletBV, hDrift⟩ :=
    exercise42AvramLevyTripletBridgeV1 P F L hBV
  have hRep := bvActualJumpDriftRepresentationV1 P L.X hLevy
    triplet hTriplet hTripletBV Xleft hLeft
  have hPos := exercise42PositiveSupremumV1 P F L hBV hd
  have hMon := bv_actual_levy_residual_ae_monotone_all_times L hBV
  filter_upwards [hLeft, hRep, hPos, hMon] with omega hl hr hpos hm
  refine ⟨?_, hl, ?_, ?_, hpos, hm⟩
  · intro t
    refine ⟨L.rightCont omega t, ?_⟩
    by_cases ht : 0 < t
    · exact L.leftLim omega t ht
    · have hz : t = 0 := le_antisymm (le_of_not_gt ht) zero_le
      subst t
      exact ⟨L.X 0 omega, by simp⟩
  · intro t ht
    exact L.noPosJumps omega t (Xleft t omega) ht (hl t ht)
  · intro t
    simpa only [hDrift] using hr t
