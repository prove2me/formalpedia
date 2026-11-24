-- Prove2me | solution 1 for Kyprianou.Ch02.levyTimeTestKernelMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:00:17.296912+00:00
-- url     : https://prove2.me/submissions/6e9d6d9f-2347-47e2-a6fb-b677cc512a0c

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_measurableUniversalRightTimeEvaluationV1
import Theorems.Thm_Kyprianou_Ch02_cadlagWholePathAEMeasurableOfCoordinatesV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P)
    (H : ℝ → ℂ) (hH : Measurable H) :
    Measurable (fun r : ℝ => ∫ ω, H (X r.toNNReal ω) ∂P) := by
  obtain ⟨E, hE, hEval⟩ := Kyprianou.Ch02.measurableUniversalRightTimeEvaluationV1
  let A (ω : Ω) : ℝ≥0 → ℝ := fun t => X t ω
  have hA : AEMeasurable A P := Kyprianou.Ch02.cadlagWholePathAEMeasurableOfCoordinatesV1
    P X hX.cadlag_ae (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX)
  let F (p : ℝ × Ω) := H (E (hA.mk A p.2, p.1.toNNReal))
  have hF : Measurable F := hH.comp (hE.comp
    ((hA.measurable_mk.comp measurable_snd).prodMk
      (measurable_real_toNNReal.comp measurable_fst)))
  have heq : (fun r : ℝ => ∫ ω, F (r, ω) ∂P) =
      (fun r : ℝ => ∫ ω, H (X r.toNNReal ω) ∂P) := by
    funext r
    apply integral_congr_ae
    filter_upwards [hA.ae_eq_mk, hX.cadlag_ae] with ω ha hc
    dsimp [F]
    rw [← ha, hEval (A ω) (fun t => (hc t).1)]
  rw [← heq]
  exact hF.stronglyMeasurable.integral_prod_right'.measurable
