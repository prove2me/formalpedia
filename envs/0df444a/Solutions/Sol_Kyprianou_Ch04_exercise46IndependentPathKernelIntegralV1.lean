-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46IndependentPathKernelIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:24:47.524833+00:00
-- url     : https://prove2.me/submissions/17de5eac-9f16-42f3-819f-0bac957dff84

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Fubini identity for a bounded measurable kernel of independent random variables. -/
theorem solution
    {Omega S : Type} [MeasurableSpace Omega] [MeasurableSpace S]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (J : Omega → Real) (hJ : AEMeasurable J P)
    (Z : Omega → S) (hZ : AEMeasurable Z P)
    (hInd : IndepFun J Z P)
    (f : Real × S → Real) (hf : Measurable f)
    (hBound : ∀ z, ‖f z‖ ≤ 1) :
    (∫ w, f (J w, Z w) ∂P) =
      ∫ y, (∫ w, f (y, Z w) ∂P) ∂(P.map J) := by
  letI : IsFiniteMeasure (P.map J) := Measure.isFiniteMeasure_map _ _
  letI : IsFiniteMeasure (P.map Z) := Measure.isFiniteMeasure_map _ _
  have hInt : Integrable f ((P.map J).prod (P.map Z)) :=
    (integrable_const (1 : Real)).mono' hf.aestronglyMeasurable (Eventually.of_forall hBound)
  calc
    _ = ∫ z, f z ∂(P.map (fun w => (J w, Z w))) :=
      (integral_map (hJ.prodMk hZ) hf.aestronglyMeasurable).symm
    _ = ∫ z, f z ∂(P.map J).prod (P.map Z) := by
      rw [hInd.map_prod_eq_prod_map_map hJ hZ]
    _ = ∫ y, (∫ z, f (y, z) ∂(P.map Z)) ∂(P.map J) := integral_prod f hInt
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      exact integral_map hZ
        (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
