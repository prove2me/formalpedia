-- Prove2me | solution 1 for Kyprianou.Ch03.canonicalZeroOriginProductTransportV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:18:47.796839+00:00
-- url     : https://prove2.me/submissions/71619538-eeaf-4fe5-aa88-1c0b6c921353

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (μ : Measure (NNReal → ℝ)) [IsProbabilityMeasure μ]
    (h0 : ∀ᵐ f ∂μ, f 0 = 0) :
    ∃ Q : Measure {path : NNReal → ℝ // path 0 = 0}, IsProbabilityMeasure Q ∧
      ∀ I : Finset NNReal,
        Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) Q =
          Measure.map (I.restrict (π := fun _ : NNReal => ℝ)) μ := by
  classical
  let patch : (NNReal → ℝ) → {path : NNReal → ℝ // path 0 = 0} :=
    fun f => ⟨fun t => if t = 0 then 0 else f t, by simp⟩
  have hp : Measurable patch := by
    apply Measurable.subtype_mk
    apply measurable_pi_lambda
    intro t
    by_cases ht : t = 0
    · simp [ht]
    · simpa [ht] using (measurable_pi_apply t : Measurable (fun f : NNReal → ℝ => f t))
  let Q := μ.map patch
  have hQ : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map hp.aemeasurable
  refine ⟨Q, hQ, ?_⟩
  intro J
  have hres : Measurable (fun w : {path : NNReal → ℝ // path 0 = 0} => J.restrict w.val) := (Finset.measurable_restrict (X := fun _ : NNReal => ℝ) J).comp
    (measurable_subtype_coe : Measurable (Subtype.val : {path : NNReal → ℝ // path 0 = 0} → _))
  change Measure.map (fun w => J.restrict w.val) (μ.map patch) = _
  rw [Measure.map_map hres hp]
  have he : ((fun w : {path : NNReal → ℝ // path 0 = 0} => J.restrict w.val) ∘ patch) =ᵐ[μ]
      J.restrict := by
    filter_upwards [h0] with f hf
    funext j
    change (if (j : NNReal) = 0 then 0 else f j) = f j
    by_cases hj : (j : NNReal) = 0 <;> simp [hj, hf]
  exact Measure.map_congr he
