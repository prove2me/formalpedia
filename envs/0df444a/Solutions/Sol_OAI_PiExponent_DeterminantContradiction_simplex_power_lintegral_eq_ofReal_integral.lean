-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral_eq_ofReal_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:53:45.720693+00:00
-- url     : https://prove2.me/submissions/2d96c499-3a02-4a26-b68b-3c0568c37424

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_cutoff_integrable

open scoped BigOperators
open MeasureTheory

theorem solution (m : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
      if 0 ≤ t ∧ t < T then ENNReal.ofReal (((T - t) / T) ^ m)
      else 0) =
      ENNReal.ofReal (MeasureTheory.integral MeasureTheory.volume (fun t : Real =>
        if 0 ≤ t ∧ t < T then ((T - t) / T) ^ m else 0)) := by
  let f : Real → Real := fun t =>
    if 0 ≤ t ∧ t < T then ((T - t) / T) ^ m else 0
  have hf : Integrable f MeasureTheory.volume :=
    OAI.PiExponent.DeterminantContradiction.cutoff_integrable m T hT
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume] f :=
    Filter.Eventually.of_forall fun t => by
      dsimp [f]
      by_cases h : 0 ≤ t ∧ t < T
      · simp only [if_pos h]
        have hbase : 0 ≤ (T - t) / T := by
          apply div_nonneg
          · linarith [h.2]
          · exact le_of_lt hT
        positivity
      · simp [h]
  have hfun :
      (fun t : Real =>
        if 0 ≤ t ∧ t < T then ENNReal.ofReal (((T - t) / T) ^ m) else 0) =
      (fun t : Real => ENNReal.ofReal (f t)) := by
    funext t
    by_cases h : 0 ≤ t ∧ t < T <;> simp [f, h]
  rw [hfun]
  exact (ofReal_integral_eq_lintegral_ofReal hf hnonneg).symm