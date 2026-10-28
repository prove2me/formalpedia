-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexSlices_lintegral_eval
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:10:43.950659+00:00
-- url     : https://prove2.me/submissions/4fdd49cf-b807-416e-811d-2c62d2e478bc

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlices_volume_scale
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlices_scalar_lintegral

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem solution (n : Nat) :
    (∫⁻ t : Real,
      (if t ∈ Set.Icc (0 : Real) 1 then
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
            (Finset.univ.sum fun i : Fin n => x i) ≤ 1 - t}
      else 0) ∂MeasureTheory.volume) =
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
          (Finset.univ.sum fun i : Fin n => x i) ≤ 1} *
        ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) := by
  let simplex : Set (Fin n → Real) :=
    {x | (∀ i, 0 ≤ x i) ∧ (Finset.univ.sum fun i : Fin n => x i) ≤ 1}
  have hscale (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
      MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
            (Finset.univ.sum fun i : Fin n => x i) ≤ 1 - t} =
        MeasureTheory.volume simplex * ENNReal.ofReal ((1 - t) ^ n) := by
    simpa [simplex] using
      OAI.PiExponent.DeterminantContradiction.unitSimplexSlices_volume_scale n t ht
  calc
    (∫⁻ t : Real,
      (if t ∈ Set.Icc (0 : Real) 1 then
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
            (Finset.univ.sum fun i : Fin n => x i) ≤ 1 - t}
      else 0) ∂MeasureTheory.volume) =
        (∫⁻ t : Real,
          (if t ∈ Set.Icc (0 : Real) 1 then
            MeasureTheory.volume simplex * ENNReal.ofReal ((1 - t) ^ n)
          else 0) ∂MeasureTheory.volume) := by
            apply lintegral_congr_ae
            filter_upwards with t
            by_cases ht : t ∈ Set.Icc (0 : Real) 1
            · simp [ht, hscale t ht]
            · simp [ht]
    _ = MeasureTheory.volume simplex *
          ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) := by
          exact OAI.PiExponent.DeterminantContradiction.unitSimplexSlices_scalar_lintegral
            n (MeasureTheory.volume simplex)
    _ = MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
            (Finset.univ.sum fun i : Fin n => x i) ≤ 1} *
          ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) := by
          rfl