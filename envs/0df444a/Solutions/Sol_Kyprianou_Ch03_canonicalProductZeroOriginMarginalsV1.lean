-- Prove2me | solution 1 for Kyprianou.Ch03.canonicalProductZeroOriginMarginalsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:18:04.399662+00:00
-- url     : https://prove2.me/submissions/42fcedd2-d079-45e1-b762-484310a2d145

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_canonicalProductZeroOriginAEV1
import Theorems.Thm_Kyprianou_Ch03_canonicalZeroOriginProductTransportV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (μ : Measure (NNReal → ℝ)) [IsProbabilityMeasure μ]
    (M : NNReal → Measure {path : NNReal → ℝ // path 0 = 0})
    (hProj : ∀ I : Finset NNReal,
      Measure.map (I.restrict (π := fun _ : NNReal => ℝ)) μ =
        Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) (M (I.sup id))) :
    ∃ Q : Measure {path : NNReal → ℝ // path 0 = 0}, IsProbabilityMeasure Q ∧
      ∀ I : Finset NNReal,
        Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) Q =
          Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) (M (I.sup id)) := by
  have h0 := Kyprianou.Ch03.canonicalProductZeroOriginAEV1 μ M hProj
  obtain ⟨Q, hQ, hm⟩ := Kyprianou.Ch03.canonicalZeroOriginProductTransportV1 μ h0
  exact ⟨Q, hQ, fun I => (hm I).trans (hProj I)⟩
