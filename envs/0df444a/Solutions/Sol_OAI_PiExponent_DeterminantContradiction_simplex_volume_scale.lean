-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_scale
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:56:10.94101+00:00
-- url     : https://prove2.me/submissions/92356de5-f605-4173-8d34-1e22257b0612

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_preimage_eq
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_measurable
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_preimage_smul

open scoped BigOperators
open MeasureTheory

theorem solution (m : Nat) (s T : Real) (hs : 0 < s) (hT : 0 < T) :
    MeasureTheory.volume {x : Fin m → Real |
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < s} =
      ENNReal.ofReal ((s / T) ^ m) *
        MeasureTheory.volume {x : Fin m → Real |
          (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} := by
  have hpre := OAI.PiExponent.DeterminantContradiction.simplex_preimage_eq
    m s T hs hT
  have hscale := OAI.PiExponent.DeterminantContradiction.volume_preimage_smul
    m (T / s) (div_pos hT hs)
    {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T}
    (OAI.PiExponent.DeterminantContradiction.simplex_measurable m T)
  have hinv : (T / s)⁻¹ = s / T := by
    field_simp [ne_of_gt hs, ne_of_gt hT] <;> ring
  calc
    MeasureTheory.volume {x : Fin m → Real |
        (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < s} =
        MeasureTheory.volume ((fun x => (T / s) • x) ⁻¹'
          {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T}) :=
            congrArg MeasureTheory.volume hpre
    _ = ENNReal.ofReal (((T / s)⁻¹) ^ m) *
        MeasureTheory.volume {x : Fin m → Real |
          (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} := hscale
    _ = ENNReal.ofReal ((s / T) ^ m) *
        MeasureTheory.volume {x : Fin m → Real |
          (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} := by rw [hinv]