-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_slice_aux
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:20:36.844786+00:00
-- url     : https://prove2.me/submissions/5a63e137-c46f-4aeb-be75-9df0c0d4514f

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_succ_slice_lintegral
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_scale
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_power_lintegral
open scoped BigOperators
open MeasureTheory

theorem solution (m : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.volume {x : Fin (m + 1) → Real |
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} =
      ENNReal.ofReal (T / ((m + 1 : Nat) : Real)) *
        MeasureTheory.volume {x : Fin m → Real |
          (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_slice_lintegral
    m T hT]
  have hslices :
      (fun t : Real =>
        if 0 ≤ t ∧ t < T then
          MeasureTheory.volume {x : Fin m → Real |
            (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T - t}
        else 0) =
      (fun t : Real =>
        if 0 ≤ t ∧ t < T then
          ENNReal.ofReal (((T - t) / T) ^ m) *
            MeasureTheory.volume {x : Fin m → Real |
              (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T}
        else 0) := by
    funext t
    by_cases ht : 0 ≤ t ∧ t < T
    · have hpos : 0 < T - t := sub_pos.mpr ht.2
      simpa only [if_pos ht] using
        (OAI.PiExponent.DeterminantContradiction.simplex_volume_scale
          m (T - t) T hpos hT)
    · simp only [if_neg ht]
  rw [hslices]
  exact
    OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral
      m T hT
      (MeasureTheory.volume {x : Fin m → Real |
        (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T})