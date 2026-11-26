-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FutureFunctionalOccupationV26
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:43:56.325546+00:00
-- url     : https://prove2.me/submissions/fda25aac-5b5e-46d2-94c9-53016b56c839

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41IndependentLevelNullV23
import Theorems.Thm_Kyprianou_Ch04_exercise41AllLevelsOccupationV16
import Theorems.Thm_Kyprianou_Ch04_exercise41FutureFunctionalLawV24
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance) (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) (G : (NNReal → ℝ) → ℝ) (hG : Measurable G) :
    ∀ᵐ w ∂P, volume {s : ℝ | 0 ≤ s ∧ L.X s.toNNReal w +
      G (fun t => L.X (s.toNNReal + t) w - L.X s.toNNReal w) = 0} = 0 := by
  letI : IsProbabilityMeasure P := L.isProbability
  let μ : Measure ℝ := Measure.map (fun w => G (fun t => L.X t w)) P
  have hOrigin : Measurable (fun w => G (fun t => L.X t w)) :=
    hG.comp (measurable_pi_lambda _ (fun t => (L.adapted t).mono (F.le t) le_rfl))
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hOrigin.aemeasurable
  have hx := rightContinuous_measurable_sections_joint_evaluation L.X
    (fun t => (L.adapted t).mono (F.le t) le_rfl) L.rightCont
  let X : ℝ × Ω → ℝ := fun p => L.X p.1.toNNReal p.2
  let Y : ℝ × Ω → ℝ := fun p => G (fun t => L.X (p.1.toNNReal+t) p.2 - X p)
  have hX : Measurable X := hx.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hY : Measurable Y := hG.comp (measurable_pi_lambda _ (fun t =>
    (hx.comp (((measurable_real_toNNReal.comp measurable_fst).add measurable_const).prodMk measurable_snd)).sub hX))
  have hOcc : ∀ᵐ w ∂P, ∀ b : ℝ, volume {s : ℝ | 0 ≤ s ∧ X (s,w) = b} = 0 :=
    exercise41AllLevelsOccupationV16 P F L hBV hd
  have hLaw (s : ℝ) (_ : 0 ≤ s) :
      Measure.map (fun w => (X (s,w), Y (s,w))) P =
      (Measure.map (fun w => X (s,w)) P).prod μ :=
    exercise41FutureFunctionalLawV24 P F L s.toNNReal G hG
  exact exercise41IndependentLevelNullV23 P μ X Y hX hY hOcc hLaw

