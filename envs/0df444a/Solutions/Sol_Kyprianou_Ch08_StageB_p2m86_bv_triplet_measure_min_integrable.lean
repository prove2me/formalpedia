-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m86_bv_triplet_measure_min_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:10:19.035183+00:00
-- url     : https://prove2.me/submissions/c382a6c0-8429-475c-a50d-4c29a209b731

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Integrability is carried by the Lévy measure field in the triplet. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P),
    Integrable (fun y : ℝ => min 1 (y ^ 2)) D.triplet.levyMeasure := by
  intro Ω mΩ P hP D
  have hstrong : AEStronglyMeasurable
      (fun y : ℝ => min 1 (y ^ 2)) D.triplet.levyMeasure := by
    exact (measurable_const.min (measurable_id'.pow_const 2)).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[D.triplet.levyMeasure]
      (fun y : ℝ => min 1 (y ^ 2)) := by
    filter_upwards [] with y
    exact le_min (by norm_num) (sq_nonneg y)
  exact (lintegral_ofReal_ne_top_iff_integrable hstrong hnonneg).mp
    (ne_of_lt D.triplet.levyMeasure_isLevyMeasure.2)
