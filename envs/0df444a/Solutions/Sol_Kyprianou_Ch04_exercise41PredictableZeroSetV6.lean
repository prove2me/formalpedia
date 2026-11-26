-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41PredictableZeroSetV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:22:55.272303+00:00
-- url     : https://prove2.me/submissions/862ad162-2c44-4733-9b3f-4b5413881346

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableLeftVersionV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (T : NNReal) :
    let E : Set (NNReal × Ω) := {p | 0 < p.1 ∧ p.1 ≤ T ∧
      Function.leftLim (fun t => L.X t p.2) p.1 = 0}
    MeasurableSet[F.rightCont.predictable] E ∧ MeasurableSet E := by
  let V : NNReal → Ω → ℝ := fun t w => Function.leftLim (fun s => L.X s w) t
  have hV : IsStronglyPredictable F V :=
    Kyprianou.Ch04.predictableLeftVersionV1 F L.X L.adapted.stronglyAdapted L.leftLim
  have hle : F.predictable ≤ F.rightCont.predictable := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      apply measurableSet_predictable_singleton_bot_prod
      exact F.le_rightCont _ _ hA
    · intro i A hA
      apply measurableSet_predictable_Ioi_prod
      exact F.le_rightCont _ _ hA
  have hz : MeasurableSet[F.predictable] {p : NNReal × Ω | V p.1 p.2 = 0} :=
    hV.measurable (measurableSet_singleton (0 : ℝ))
  have hclock : MeasurableSet[F.predictable] (Ioc (0 : NNReal) T ×ˢ (univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod 0 T MeasurableSet.univ
  have he : MeasurableSet[F.predictable] {p : NNReal × Ω |
      0 < p.1 ∧ p.1 ≤ T ∧ V p.1 p.2 = 0} := by
    convert hclock.inter hz using 1
    ext p
    simp [and_assoc]
  refine ⟨hle _ he, ?_⟩
  apply measurableSpace_le_predictable_of_measurableSet
    (𝓕 := F) (m' := inferInstance) (fun A hA => ?_) (fun i A hA => ?_) _ he
  · exact (measurableSet_singleton _).prod (F.le _ _ hA)
  · exact measurableSet_Ioi.prod (F.le _ _ hA)
