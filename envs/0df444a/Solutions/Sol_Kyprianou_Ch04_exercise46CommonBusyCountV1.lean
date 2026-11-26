-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46CommonBusyCountV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:21:42.790492+00:00
-- url     : https://prove2.me/submissions/769862ba-31a1-4edc-88af-3c39a8952de2

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46BusyDrawdownFunctionalV1
import Theorems.Thm_Kyprianou_Ch04_exercise46BusyPathCountFunctionalV1
import Theorems.Thm_Kyprianou_Ch04_exercise46RawSupEqualsRunningSupV1
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (Wleft : NNReal → Omega → Real)
    (hWLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s : NNReal =>
        sSup ((fun u => L.X u w) '' Iic s) - L.X s w)
        (nhdsWithin t (Iio t)) (nhds (Wleft t w))) :
    ∃ C : (NNReal → Real) → ENNReal, Measurable C ∧
      (∀ᵐ w ∂P, C (fun t => L.X t w) =
        (({t : NNReal | 0 < t ∧ Wleft t w = 0 ∧
          0 < sSup ((fun u => L.X u w) '' Iic t) - L.X t w}).encard : ENNReal)) ∧
      (∀ w s, let Y : NNReal → Real := fun t => L.X (s+t) w - L.X s w
        C Y = (({t : NNReal | 0 < t ∧ sSup (Y '' Iic t) = Function.leftLim Y t ∧
          Y t < Function.leftLim Y t}).encard : ENNReal)) := by
  obtain ⟨D, hD, hFresh, hShift⟩ :=
    Kyprianou.Ch04.exercise46BusyDrawdownFunctionalV1 P G L
  obtain ⟨C, hC, hCount⟩ := Kyprianou.Ch04.exercise46BusyPathCountFunctionalV1 D hD
  refine ⟨C,hC,?_,?_⟩
  · filter_upwards [hWLeft] with w hw
    obtain ⟨hRight,hLeft⟩ := avram_wave7_01_original_shifted_future_increment_path_cadlag L w 0
    simp only [zero_add, L.X_zero, sub_zero] at hRight hLeft
    rw [hCount _ hRight hLeft]
    apply congrArg (fun S : Set NNReal => (S.encard : ENNReal))
    ext t
    by_cases ht : 0 < t
    · letI : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,ht⟩
      have h := hw t ht
      simp_rw [Kyprianou.Ch04.exercise46RawSupEqualsRunningSupV1 P G L w] at h
      have hL := (avram_p2_a_zero_rate_original_cadlag_regular_all_times L w).1 t
      have hS := ((runningSup_continuous_actual L w).continuousAt (x := t)).tendsto
      have he := tendsto_nhds_unique h ((hS.mono_left nhdsWithin_le_nhds).sub hL)
      simp only [mem_setOf_eq, ht, true_and, hFresh w t,
        Kyprianou.Ch04.exercise46RawSupEqualsRunningSupV1 P G L w t, he]
      constructor
      · rintro ⟨hp,heq⟩
        exact ⟨by linarith, hp⟩
      · rintro ⟨heq,hp⟩
        exact ⟨hp,by linarith⟩
    · simp [ht]
  · intro w s
    dsimp only
    obtain ⟨hRight,hLeft⟩ := avram_wave7_01_original_shifted_future_increment_path_cadlag L w s
    rw [hCount _ hRight hLeft]
    apply congrArg (fun S : Set NNReal => (S.encard : ENNReal))
    ext t
    simp only [mem_setOf_eq,hShift w s t]
    constructor
    · rintro ⟨ht,hp,he⟩
      exact ⟨ht,by linarith,by linarith⟩
    · rintro ⟨ht,he,hp⟩
      exact ⟨ht,by linarith,by linarith⟩
