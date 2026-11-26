-- Prove2me | solution 1 for Kyprianou.Ch04.closedStopMaskLeftLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:20:51.790262+00:00
-- url     : https://prove2.me/submissions/b2c8df5e-c2bc-430c-9dee-1e3a342614b3

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Multiplication by the closed stopping mask preserves positive-time left limits. -/
theorem solution (k : ℝ → ℝ) (tau : WithTop NNReal) (t : NNReal) (ht : 0 < t)
    (hk : Tendsto k (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ))) (nhds (k (t : ℝ)))) :
    Tendsto (fun s : ℝ => if (s.toNNReal : WithTop NNReal) ≤ tau then k s else 0)
      (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
      (nhds (if (t : WithTop NNReal) ≤ tau then k (t : ℝ) else 0)) := by
  by_cases h : (t : WithTop NNReal) ≤ tau
  · rw [if_pos h]
    apply hk.congr'
    filter_upwards [self_mem_nhdsWithin (a := (t : ℝ)) (s := Set.Iio (t : ℝ))] with s hs
    have hst : s.toNNReal ≤ t := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hs.le
    exact (if_pos ((WithTop.coe_le_coe.mpr hst).trans h)).symm
  · rw [if_neg h]
    induction tau using WithTop.recTopCoe with
    | top => exact False.elim (h le_top)
    | coe a =>
      have ha : a < t := lt_of_not_ge (fun hta => h (WithTop.coe_le_coe.mpr hta))
      have har : (a : ℝ) < (t : ℝ) := by exact_mod_cast ha
      have hev : ∀ᶠ s in nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)), (a : ℝ) < s :=
        mem_of_superset (nhdsWithin_le_nhds (Ioi_mem_nhds har)) (fun _ hs => hs)
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with s hs
      have hs' : a < s.toNNReal := by
        have hnon : 0 ≤ s := (NNReal.coe_nonneg a).trans hs.le
        exact NNReal.coe_lt_coe.mp (by rwa [Real.coe_toNNReal _ hnon])
      exact (if_neg (not_le_of_gt (WithTop.coe_lt_coe.mpr hs'))).symm
