-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49DepthProductPushforwardV7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:41:19.372674+00:00
-- url     : https://prove2.me/submissions/3a2b188e-ed17-4457-8e36-a25172987ab8

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49RationalDepthMeasV1
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Set Ω) (I : Ω → ℝ) (Z H : Ω → NNReal → ℝ)
    (hI : Measurable I) (hZ : Measurable Z) (hH : Measurable H)
    (hJoint : Measure.map (fun w => (I w,Z w)) (P.restrict D) =
      (Measure.map I (P.restrict D)).prod (Measure.map H P)) :
    let d : (NNReal → ℝ) → ℝ := fun y => (⨆ q : ℚ, ENNReal.ofReal (-y (Real.toNNReal q))).toReal
    Measure.map (fun w => (I w,d (Z w))) (P.restrict D) =
      (Measure.map I (P.restrict D)).prod (Measure.map (d ∘ H) P) := by
  intro d
  have hd : Measurable d := Kyprianou.Ch04.exercise49RationalDepthMeasV1
  have hp : Measurable (Prod.map (id : ℝ → ℝ) d) := measurable_id.prodMap hd
  have he := congrArg (Measure.map (Prod.map (id : ℝ → ℝ) d)) hJoint
  rw [Measure.map_map hp (hI.prodMk hZ),← Measure.map_prod_map _ _ measurable_id hd,
    Measure.map_id,Measure.map_map hd hH] at he
  exact he
