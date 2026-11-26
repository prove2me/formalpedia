-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_5_ii_goalV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:38:19.42386+00:00
-- url     : https://prove2.me/submissions/d600349c-0a4d-4ddc-9237-bc304905bede

import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_cutoffCauchyFromTerminalEnergyV1
import Theorems.Thm_Kyprianou_Ch04_finiteWindowWeightedL2V1
import Theorems.Thm_Kyprianou_Ch04_exercise45ActualCutoffRightV1
import Theorems.Thm_Kyprianou_Ch04_exercise45ActualCutoffEnergyV1
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Reduce the actual cutoff Cauchy certificate to its regularity and energy obligations. -/
theorem solution : Kyprianou.Ch04.certificate_ex4_5_iiV3 := by
  unfold Kyprianou.Ch04.certificate_ex4_5_iiV3
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation T hT M hM
  let ν := triplet.levyMeasure
  have hν := triplet.levyMeasure_isLevyMeasure
  have hL2 (e : ℝ) (he : 0 < e) (he1 : e < 1) : MemLp (M e T) 2 P := by
    let B : Set ℝ := {x | e < |x| ∧ |x| < 1}
    have hB : MeasurableSet B :=
      (measurableSet_lt measurable_const measurable_id.abs).inter
        (measurableSet_lt measurable_id.abs measurable_const)
    have hfin : ν B < ⊤ :=
      (measure_mono (show B ⊆ {x | e ≤ |x|} from fun x hx => hx.1.le)).trans_lt
        (hν.measure_setOf_abs_ge_lt_top he)
    apply Kyprianou.Ch04.finiteWindowWeightedL2V1 P ν N B hB hfin T K hK.le
      (fun s x ω => x * fSpace s (XepsLeft e s.toNNReal ω)) _
      (M e T) (((hM e he he1).2.stronglyAdapted T).mono (F.le T)).aestronglyMeasurable
      ((hM e he he1).1 T)
    intro s x ω hs hx
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hx.2.le |>.trans (hBound s _ hs).2.2.1
  have hr := Kyprianou.Ch04.exercise45ActualCutoffRightV1 P F X hLevy triplet
    hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
    hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound
    Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation
    T hT M hM
  have hen := Kyprianou.Ch04.exercise45ActualCutoffEnergyV1 P F X hLevy triplet
    hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
    hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound
    Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation
    T hT M hM
  exact Kyprianou.Ch04.cutoffCauchyFromTerminalEnergyV1 P F ν hν M T hT _
    (fun e he he1 => (hM e he he1).2) hr hL2 hen
