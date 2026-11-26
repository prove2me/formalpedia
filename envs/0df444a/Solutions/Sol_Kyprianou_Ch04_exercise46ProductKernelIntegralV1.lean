-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46ProductKernelIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:43:47.623948+00:00
-- url     : https://prove2.me/submissions/0215ed7d-296a-4855-b397-f65da20b5c30

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (J : Omega → Real) (Z Y : Omega → E)
    (hJ : AEMeasurable J P) (hZ : AEMeasurable Z P) (hY : Measurable Y)
    (hLaw : P.map (fun w => (J w,Z w)) = (P.map J).prod (P.map Y))
    (f : Real × E → Real) (hf : Measurable f) (hBound : ∀ z, ‖f z‖ ≤ 1) :
    (∫ w, f (J w,Z w) ∂P) = ∫ y, (∫ w, f (y,Y w) ∂P) ∂(P.map J) := by
  letI : IsFiniteMeasure (P.map J) := Measure.isFiniteMeasure_map _ _
  letI : IsFiniteMeasure (P.map Y) := Measure.isFiniteMeasure_map _ _
  have hInt : Integrable f ((P.map J).prod (P.map Y)) :=
    (integrable_const (1 : Real)).mono' hf.aestronglyMeasurable (Eventually.of_forall hBound)
  calc
    _ = ∫ z, f z ∂(P.map (fun w => (J w,Z w))) :=
      (integral_map (hJ.prodMk hZ) hf.aestronglyMeasurable).symm
    _ = ∫ z, f z ∂(P.map J).prod (P.map Y) := by rw [hLaw]
    _ = ∫ y, (∫ z, f (y,z) ∂(P.map Y)) ∂(P.map J) := integral_prod f hInt
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      exact integral_map hY.aemeasurable
        (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
