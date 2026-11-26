-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46BusyStartsCanonicalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:49:07.490899+00:00
-- url     : https://prove2.me/submissions/93a81f35-bed2-40d8-8301-97bbc692df7b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_Kyprianou_Ch04_exercise46RawSupEqualsRunningSupV1
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (Wleft : NNReal → Omega → Real)
    (hWLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto
        (fun s : NNReal => sSup ((fun u : NNReal => L.X u w) '' Iic s) - L.X s w)
        (nhdsWithin t (Iio t)) (nhds (Wleft t w))) :
    let B : Omega → Set NNReal := fun w =>
      {t | 0 < t ∧ Wleft t w = 0 ∧
        0 < sSup ((fun u : NNReal => L.X u w) '' Iic t) - L.X t w}
    ∃ S : Set (Omega × NNReal), MeasurableSet S ∧
      (∀ w t, (w,t) ∈ S → 0 < t ∧
        L.X t w - Function.leftLim (fun u : NNReal => L.X u w) t ≠ 0) ∧
      ∀ᵐ w ∂P, B w = {t | (w,t) ∈ S} := by
  dsimp only
  let R : Omega × NNReal → Real := fun z => runningSup L z.2 z.1
  let Xl : Omega × NNReal → Real := fun z =>
    Function.leftLim (fun u : NNReal => L.X u z.1) z.2
  let Xr : Omega × NNReal → Real := fun z => L.X z.2 z.1
  let S : Set (Omega × NNReal) := {z | 0 < z.2 ∧ R z = Xl z ∧ Xr z < Xl z}
  have hR : Measurable R := (levy_runningSup_joint_time_path_measurable L).comp measurable_swap
  have hl : Measurable Xl :=
    (avram_wave4_04a_actual_levy_prejump_joint_measurable L).comp measurable_swap
  have hr : Measurable Xr := (chat04_levy_joint_time_state_measurable L).comp measurable_swap
  refine ⟨S, (measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_eq_fun hR hl).inter (measurableSet_lt hr hl)), ?_, ?_⟩
  · intro w t ht
    exact ⟨ht.1, sub_ne_zero.mpr (ne_of_lt ht.2.2)⟩
  · filter_upwards [hWLeft] with w hw
    ext t
    by_cases ht : 0 < t
    · letI : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
      have hSup := Kyprianou.Ch04.exercise46RawSupEqualsRunningSupV1 P G L w
      have h := hw t ht
      simp_rw [hSup] at h
      have hL := (avram_p2_a_zero_rate_original_cadlag_regular_all_times L w).1 t
      have hC := ((runningSup_continuous_actual L w).continuousAt (x := t)).tendsto
      have he := tendsto_nhds_unique h ((hC.mono_left nhdsWithin_le_nhds).sub hL)
      simp only [mem_setOf_eq, S, R, Xl, Xr, ht, true_and, hSup, he, sub_eq_zero,
        sub_pos]
      exact and_congr_right (fun h => by rw [h])
    · simp [S, ht]
