-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46LeftLimitMeshConvergenceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:10:18.21638+00:00
-- url     : https://prove2.me/submissions/c3e12764-e250-4f0d-8282-ced8a6810b91

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_prejump_fractional_left_time_mesh
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (f : NNReal → Real)
    (hleft : ∀ t : NNReal, 0 < t → ∃ l : Real,
      Tendsto f (nhdsWithin t (Iio t)) (nhds l))
    (t : NNReal) :
    Tendsto (fun n : Nat => f (t - t * (1 / 2 : NNReal) ^ (n + 1)))
      atTop (nhds (Function.leftLim f t)) := by
  by_cases ht : t = 0
  · subst t
    rw [leftLim_eq_of_isBot (show IsBot (0 : NNReal) from fun _ => zero_le)]
    simpa only [zero_mul, tsub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => f 0) atTop (nhds (f 0)))
  · have hp : 0 < t := pos_iff_ne_zero.mpr ht
    letI : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hp⟩
    obtain ⟨l, hl⟩ := hleft t hp
    rw [leftLim_eq_of_tendsto hl]
    have hm := avram_wave4_04b_prejump_fractional_left_time_mesh
    have hc : Tendsto (fun n : Nat => t - t * (1 / 2 : NNReal) ^ (n + 1))
        atTop (nhdsWithin t (Iio t)) :=
      tendsto_nhdsWithin_iff.2 ⟨hm.2.1 t, Eventually.of_forall (hm.2.2 t hp)⟩
    exact hl.comp hc
