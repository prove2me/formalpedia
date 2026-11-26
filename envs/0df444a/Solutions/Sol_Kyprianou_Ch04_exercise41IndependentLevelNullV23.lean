-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41IndependentLevelNullV23
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:07:27.126347+00:00
-- url     : https://prove2.me/submissions/8df65b8f-9481-4ef7-ae40-9de5f3e1b30c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41IndependentLevelSectionNullV23
import Theorems.Thm_Kyprianou_Ch04_exercise41IndependentLevelTransferV23
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (X Y : ℝ × Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hOcc : ∀ᵐ w ∂P, ∀ b : ℝ, volume {s : ℝ | 0 ≤ s ∧ X (s,w) = b} = 0)
    (hLaw : ∀ s : ℝ, 0 ≤ s →
      Measure.map (fun w => (X (s,w),Y (s,w))) P =
      (Measure.map (fun w => X (s,w)) P).prod μ) :
    ∀ᵐ w ∂P, volume {s : ℝ | 0 ≤ s ∧ X (s,w) + Y (s,w) = 0} = 0 := by
  have hm : MeasurableSet {p : ℝ × Ω | ¬ (0 ≤ p.1 ∧ X p + Y p = 0)} :=
    ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_eq_fun (hX.add hY) measurable_const)).compl
  have h : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ w ∂P, ¬ (0 ≤ s ∧ X (s,w) + Y (s,w) = 0) := by
    filter_upwards [exercise41IndependentLevelSectionNullV23 P μ X hX hOcc] with s hs
    by_cases hp : 0 ≤ s
    · have h' : ∀ᵐ p ∂P.prod μ, X (s,p.1) + p.2 ≠ 0 := hs.mono (fun p h => fun he => h ⟨hp,he⟩)
      have H := exercise41IndependentLevelTransferV23 P μ (fun w => X (s,w)) (fun w => Y (s,w))
        (hX.comp (measurable_const.prodMk measurable_id)) (hY.comp (measurable_const.prodMk measurable_id))
        (hLaw s hp) h'
      exact H.mono (fun w hw hbad => hw hbad.2)
    · exact Eventually.of_forall (fun _ hbad => hp hbad.1)
  filter_upwards [(Measure.ae_ae_comm hm).mp h] with w hw
  simpa only [ae_iff,not_not] using hw
