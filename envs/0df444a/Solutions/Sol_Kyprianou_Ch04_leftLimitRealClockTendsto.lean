-- Prove2me | solution 1 for Kyprianou.Ch04.leftLimitRealClockTendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:46:11.829222+00:00
-- url     : https://prove2.me/submissions/9a0c17ed-804d-4f1c-b533-6eca742b4340

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Left limits of a nonnegative-time path yield a left-continuous left-limit path on real time. -/
theorem solution (Y L : NNReal → ℝ)
    (hl : ∀ t : NNReal, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t))) :
    ∀ t : NNReal, 0 < t →
      Tendsto (fun s : ℝ => L s.toNNReal) (nhdsWithin (t : ℝ) (Iio (t : ℝ)))
        (nhds (L t)) := by
  intro t ht
  have he (u : NNReal) (hu : 0 < u) : Function.leftLim Y u = L u := by
    haveI : (nhdsWithin u (Iio u)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,hu⟩
    exact leftLim_eq_of_tendsto (hl u hu)
  have hlim : Tendsto Y (nhdsWithin t (Iio t)) (nhds (Function.leftLim Y t)) := by
    rw [he t ht]
    exact hl t ht
  have hmap : Tendsto Real.toNNReal (nhdsWithin (t : ℝ) (Iio (t : ℝ)))
      (nhdsWithin t (Iic t)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using continuous_real_toNNReal.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (t : ℝ)) (s := Iio (t : ℝ)))
    · filter_upwards [self_mem_nhdsWithin (a := (t : ℝ)) (s := Iio (t : ℝ))] with s hs
      exact Real.toNNReal_le_iff_le_coe.mpr hs.le
  have h := (continuousWithinAt_leftLim_Iic hlim).tendsto.comp hmap
  rw [he t ht] at h
  apply h.congr'
  have htp : (0 : ℝ) < t := by exact_mod_cast ht
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds htp)] with s hs
  exact he s.toNNReal (Real.toNNReal_pos.mpr hs)
