-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ZeroIntensityPRM
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:03:47.77395+00:00
-- url     : https://prove2.me/submissions/b941c006-e90c-471c-b711-f81dcd9a2f26

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch04_ito43_ce_binary_events_factor
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The zero-intensity PRM can be identically the zero measure. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    ∃ N : PoissonRandomMeasure.{0,0,0} P (0 : Measure ℝ), ∀ w, N.N w = 0 := by
  classical
  have hPois : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
    apply Measure.ext_of_singleton
    intro n
    cases n with
    | zero => simp [poissonMeasure_singleton]
    | succ n => simp [poissonMeasure_singleton]
  have hInt : referenceIntensity (0 : Measure ℝ) = 0 := by
    simp [referenceIntensity]
  refine ⟨⟨fun _ => 0, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ => rfl⟩
  · intro B hB
    exact measurable_const
  · intro B hB hf
    exact Filter.Eventually.of_forall (fun _ => ⟨0, by simp⟩)
  · intro B hB hf
    simp [hInt] at hf
  · intro B hB hf
    simp [hInt, poissonMeasureENN, hPois, Measure.map_const, Measure.map_dirac]
  · intro ι hι B hB hd
    rw [iIndepFun_iff]
    intro S A hA
    have hs (k : ι) (hk : k ∈ S) : A k = ∅ ∨ A k = univ := by
      apply MeasurableSpace.measurableSet_bot_iff.mp
      have H := hA k hk
      change MeasurableSet[MeasurableSpace.comap (fun _ : Ω => (0 : ENNReal)) inferInstance] (A k) at H
      rwa [MeasurableSpace.comap_const] at H
    exact Kyprianou.Ch04.ito43_ce_binary_events_factor P S A hs
  · intro s t hs ht A hA hfin
    simp only [MeasureTheory.Measure.coe_zero, MeasurableSpace.comap_const]
    exact indep_bot_right _
