-- Prove2me | solution 1 for Kyprianou.Ch04.pathJumpMeasureCountV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:46:53.28037+00:00
-- url     : https://prove2.me/submissions/9c2ec474-3be4-4770-a513-89eb14320dea

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Path jump measure on an arbitrary measurable set is the exact count of marked times. -/
theorem solution {Ω : Type} (X L : NNReal → Ω → ℝ) (ω : Ω)
    (hX : Measurable (fun t => X t ω)) (hL : Measurable (fun t => L t ω))
    (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) :
    Kyprianou.Ch04.pathJumpMeasure X L ω A =
      ({t : NNReal | 0 < t ∧ X t ω ≠ L t ω ∧
        ((t : ℝ), X t ω - L t ω) ∈ A}).encard := by
  let Δ : NNReal → ℝ := fun t => X t ω - L t ω
  have hΔ : Measurable Δ := hX.sub hL
  have hJ : MeasurableSet {t : NNReal | 0 < t ∧ X t ω ≠ L t ω} :=
    (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_eq_fun hX hL).compl
  have hφ : Measurable (fun t : NNReal => ((t : ℝ), Δ t)) :=
    NNReal.continuous_coe.measurable.prodMk hΔ
  have hpre := hA.preimage hφ
  unfold Kyprianou.Ch04.pathJumpMeasure
  rw [Measure.map_apply hφ hA, Measure.restrict_apply hpre,
    Measure.count_apply (hpre.inter hJ)]
  apply congrArg (fun T : Set NNReal => (T.encard : ENNReal))
  ext t
  simp [Δ, Set.mem_preimage, Set.mem_inter_iff, and_assoc, and_left_comm, and_comm]
