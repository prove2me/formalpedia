-- Prove2me | solution 1 for Kyprianou.Ch02.levyWholePathLawEqOfMarginalLawsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:54:36.704474+00:00
-- url     : https://prove2.me/submissions/b3c4b16b-130f-4c95-b40b-81b43be19d53

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
import Theorems.Thm_Kyprianou_Ch02_levyZeroBasedGridLawEqOfMarginalsV1
import Theorems.Thm_AvramDividend_Classical_cross_sample_path_law_eq_of_all_finite_vector_laws
import Theorems.Thm_AvramDividend_Classical_cross_sample_finite_coord_law_of_grid_vector_law
import Theorems.Thm_AvramDividend_Classical_finite_time_set_has_monotone_zero_started_grid
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false


/-- Source-faithful Chapter 2 proof. -/
theorem solution
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hLaw : ∀ t : ℝ≥0, Measure.map (X t) P = Measure.map (Y t) Q) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X t ω) P =
      Measure.map (fun ω : Λ => fun t : ℝ≥0 => Y t ω) Q := by
  have hA := Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P X hX
  have hB := Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 Q Y hY
  let A := hA.mk (fun ω : Ω => fun t : ℝ≥0 => X t ω)
  let B := hB.mk (fun ω : Λ => fun t : ℝ≥0 => Y t ω)
  have hAm : Measurable A := hA.measurable_mk
  have hBm : Measurable B := hB.measurable_mk
  rw [Measure.map_congr hA.ae_eq_mk, Measure.map_congr hB.ae_eq_mk]
  apply AvramDividend.Classical.cross_sample_path_law_eq_of_all_finite_vector_laws
    P Q A B hAm hBm (by simp)
  intro J
  obtain ⟨t, ht, ht0, n, henum⟩ :=
    AvramDividend.Classical.finite_time_set_has_monotone_zero_started_grid J
  have hGrid := Kyprianou.Ch02.levyZeroBasedGridLawEqOfMarginalsV1
    P Q X Y hX hY hLaw t ht n ht0
  have hAeq : (fun ω : Ω => fun i : Fin n => X (t (i.val + 1)) ω) =ᵐ[P]
      (fun ω : Ω => fun i : Fin n => A ω (t (i.val + 1))) := by
    filter_upwards [hA.ae_eq_mk] with ω hω
    funext i
    exact congrFun hω _
  have hBeq : (fun ω : Λ => fun i : Fin n => Y (t (i.val + 1)) ω) =ᵐ[Q]
      (fun ω : Λ => fun i : Fin n => B ω (t (i.val + 1))) := by
    filter_upwards [hB.ae_eq_mk] with ω hω
    funext i
    exact congrFun hω _
  rw [Measure.map_congr hAeq, Measure.map_congr hBeq] at hGrid
  exact AvramDividend.Classical.cross_sample_finite_coord_law_of_grid_vector_law
    P Q A B (measurable_pi_iff.mp hAm) (measurable_pi_iff.mp hBm)
    J t n henum hGrid
