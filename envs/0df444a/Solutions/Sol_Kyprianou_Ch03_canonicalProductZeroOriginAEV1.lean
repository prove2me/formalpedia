-- Prove2me | solution 1 for Kyprianou.Ch03.canonicalProductZeroOriginAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:18:36.209405+00:00
-- url     : https://prove2.me/submissions/ad3b0f1d-5538-4577-aad7-6debba53bc61

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (μ : Measure (NNReal → ℝ))
    (M : NNReal → Measure {path : NNReal → ℝ // path 0 = 0})
    (hProj : ∀ I : Finset NNReal,
      Measure.map (I.restrict (π := fun _ : NNReal => ℝ)) μ =
        Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) (M (I.sup id))) :
    ∀ᵐ f ∂μ, f 0 = 0 := by
  classical
  let I : Finset NNReal := {0}
  let i : I := ⟨0, Finset.mem_singleton_self 0⟩
  let E : Set (∀ _ : I, ℝ) := {g | g i ≠ 0}
  have hE : MeasurableSet E := ((measurable_pi_apply i) (measurableSet_singleton 0)).compl
  rw [ae_iff]
  have h := congrArg (fun ν : Measure (∀ _ : I, ℝ) => ν E) (hProj I)
  have hr : Measurable (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) :=
    (Finset.measurable_restrict (X := fun _ : NNReal => ℝ) I).comp measurable_subtype_coe
  rw [Measure.map_apply (Finset.measurable_restrict (X := fun _ : NNReal => ℝ) I) hE,
    Measure.map_apply hr hE] at h
  have hempty : (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) ⁻¹' E = ∅ := by
    ext w
    simp [E, i, w.property]
  rw [hempty, measure_empty] at h
  exact h
