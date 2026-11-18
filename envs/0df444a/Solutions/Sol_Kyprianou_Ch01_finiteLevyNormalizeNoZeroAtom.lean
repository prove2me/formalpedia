-- Prove2me | solution 1 for Kyprianou.Ch01.finiteLevyNormalizeNoZeroAtom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:22:34.294994+00:00
-- url     : https://prove2.me/submissions/fcee0b56-0e4d-4ae5-a20a-3305052b89e1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false
/-! Normalisation of a positive finite Lévy intensity keeps its zero atom absent. -/
theorem solution
    (Λ : Measure ℝ) (hfinite : Λ Set.univ < ⊤)
    (hpositive : 0 < Λ Set.univ) (hzero : Λ {0} = 0) :
    ((FiniteMeasure.normalize (⟨Λ, ⟨hfinite⟩⟩ : FiniteMeasure ℝ) : Measure ℝ) {0}) = 0 := by
  let FM : FiniteMeasure ℝ := ⟨Λ, ⟨hfinite⟩⟩
  have hNonzero : FM ≠ 0 := by
    intro h
    have hMu : Λ = 0 := by
      have hh := congrArg (fun x : FiniteMeasure ℝ => (x : Measure ℝ)) h
      exact hh
    have hz : Λ Set.univ = 0 := by simp [hMu]
    exact (ne_of_gt hpositive) hz
  change (FiniteMeasure.normalize FM : Measure ℝ) {0} = 0
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero FM hNonzero]
  have hzFM : (FM : Measure ℝ) {0} = 0 := hzero
  rw [Measure.smul_apply, hzFM]
  simp
