-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_update_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:00:28.136886+00:00
-- url     : https://prove2.me/submissions/caadc31d-e34e-4bf0-8de0-ffbabdfd0d35

import Theorems.Thm_KSATSingleFlip_Connect_symmetric_compound_kernel_symmetric
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem solution (ν : Measure ℝ) [IsFiniteMeasure ν] (β : ℝ)
    (hfin : (ν.withDensity fun z => ENNReal.ofReal (wInt z)) Set.univ ≠ ∞) :
    Measure.map (fun z : ℝ => -z) (Rbeta β ν) = Rbeta β ν := by
  let μ : Measure ℝ := Measure.map aShift (ν.withDensity fun z => ENNReal.ofReal (wInt z))
  have ha : Measurable aShift := by unfold aShift; fun_prop
  have hmu : μ Set.univ ≠ ∞ := by
    dsimp [μ]
    rw [Measure.map_apply ha MeasurableSet.univ]
    simpa using hfin
  letI : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr hmu⟩
  have hk : Measure.map (fun z : ℝ => -z) (Kmeas ν) = Kmeas ν := by
    change Measure.map (fun z : ℝ => -z) (compoundPoisson μ ∗ Measure.map (fun z : ℝ => -z) (compoundPoisson μ)) = _
    exact symmetric_compound_kernel_symmetric μ
  unfold Rbeta
  rw [Measure.map_smul, hk]
