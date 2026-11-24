-- Prove2me | solution 1 for Kyprianou.Ch02.levyCharFunTimeMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:13:29.930446+00:00
-- url     : https://prove2.me/submissions/a8aee6d5-761e-4481-83f3-aff47372d6ba

import Theorems.Thm_Kyprianou_Ch02_measurableUniversalRightTimeEvaluationV1
import Theorems.Thm_Kyprianou_Ch02_cadlagWholePathAEMeasurableOfCoordinatesV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) (ξ : ℝ) :
    Measurable (fun r : ℝ≥0 => charFun (P.map (X r)) ξ) := by
  obtain ⟨E, hE, hEval⟩ := Kyprianou.Ch02.measurableUniversalRightTimeEvaluationV1
  let A : Ω → (ℝ≥0 → ℝ) := fun ω t => X t ω
  have hcoord := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  have hA : AEMeasurable A P :=
    Kyprianou.Ch02.cadlagWholePathAEMeasurableOfCoordinatesV1 P X hX.cadlag_ae hcoord
  let Q := P.map A
  letI : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map hA
  let F : ℝ≥0 × (ℝ≥0 → ℝ) → ℂ := fun z =>
    Complex.exp ((ξ : ℂ) * (E (z.2,z.1) : ℂ) * Complex.I)
  have hm : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => E (z.2,z.1)) :=
    hE.comp (measurable_snd.prodMk measurable_fst)
  have hF : Measurable F := by unfold F; fun_prop
  have hInt := (hF.stronglyMeasurable.integral_prod_right' (ν := Q)).measurable
  convert hInt using 1
  funext r
  rw [charFun_apply_real, integral_map (hcoord r) (by fun_prop)]
  have hFr : Measurable (fun y : ℝ≥0 → ℝ => F (r,y)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [show Q = P.map A from rfl, integral_map hA hFr.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hX.cadlag_ae] with ω hω
  simp only [F, A, hEval _ (fun t => (hω t).1)]
