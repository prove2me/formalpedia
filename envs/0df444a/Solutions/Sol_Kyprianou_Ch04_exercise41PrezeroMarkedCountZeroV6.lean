-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41PrezeroMarkedCountZeroV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:31:38.888921+00:00
-- url     : https://prove2.me/submissions/bd85ec1e-d4a7-44e1-b57f-d16393a01e27

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46PredictableMarkedCountMeanV1
import Theorems.Thm_Kyprianou_Ch04_exercise46RightContPhysicalMarkedKernelV1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_joint_original_predictable_mark_lift_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (G : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P G) (T : NNReal)
    (E : Set (NNReal × Ω)) (hE : MeasurableSet[G.rightCont.predictable] E)
    (hT : ∀ p ∈ E, p.1 ≤ T)
    (hnull : ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal).prod P) E = 0) :
    let NX : Ω → Measure (NNReal × ℝ) := fun w =>
      ((Measure.count.restrict {u : NNReal | 0 < u ∧ L.X u w -
        Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0}).map
        (fun u => (u,L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)))
    ∀ᵐ w ∂P, NX w {p | (p.1,w) ∈ E ∧ p.2 < 0} = 0 := by
  letI : IsProbabilityMeasure P := L.isProbability
  let NX : Ω → Measure (NNReal × ℝ) := fun w =>
    ((Measure.count.restrict {u : NNReal | 0 < u ∧ L.X u w -
      Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0}).map
      (fun u => (u,L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)))
  let K : Ω → @Measure ((NNReal × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ G.rightCont.predictable
        (inferInstance : MeasurableSpace ℝ)) := fun w =>
    @Measure.map (NNReal × ℝ) ((NNReal × Ω) × ℝ) inferInstance
      (@Prod.instMeasurableSpace _ _ G.rightCont.predictable
        (inferInstance : MeasurableSpace ℝ)) (fun p => ((p.1,w),p.2)) (NX w)
  have hmean := exercise46PredictableMarkedCountMeanV1 P G L T E hE hT
    (Iio (0 : ℝ)) measurableSet_Iio subset_rfl
  dsimp only at hmean
  rw [hnull, zero_mul] at hmean
  have hK := exercise46RightContPhysicalMarkedKernelV1 P G L
  letI : MeasurableSpace (NNReal × Ω) := G.rightCont.predictable
  have hR : MeasurableSet (E ×ˢ Iio (0 : ℝ)) := hE.prod measurableSet_Iio
  have he (w : Ω) : K w (E ×ˢ Iio (0 : ℝ)) =
      NX w {p | (p.1,w) ∈ E ∧ p.2 < 0} :=
    Measure.map_apply
      ((avram_wave5_02a_joint_original_predictable_mark_lift_measurable G.rightCont).comp
        (measurable_id.prodMk measurable_const)) hR
  have hm : AEMeasurable (fun w => NX w {p | (p.1,w) ∈ E ∧ p.2 < 0}) P := by
    have H : AEMeasurable (fun w => K w (E ×ˢ Iio (0 : ℝ))) P :=
      (Measure.measurable_coe hR).comp_aemeasurable hK
    exact H.congr (Filter.Eventually.of_forall he)
  exact (lintegral_eq_zero_iff' hm).mp hmean
