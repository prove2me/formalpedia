-- Prove2me | solution 1 for Kyprianou.Ch03.temperedStableProductDifferenceCharV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:58:35.008382+00:00
-- url     : https://prove2.me/submissions/da6c68f7-a3d5-475a-9173-9fcb21f9dabf

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {OmegaP OmegaM : Type} [MeasurableSpace OmegaP] [MeasurableSpace OmegaM]
    (PP : Measure OmegaP) (PM : Measure OmegaM)
    [IsProbabilityMeasure PP] [IsProbabilityMeasure PM]
    (U : OmegaP → ℝ) (V : OmegaM → ℝ)
    (hU : Measurable U) (hV : Measurable V) (xi : ℝ) :
    charFun ((PP.prod PM).map (fun z => U z.1 - V z.2)) xi =
      charFun (PP.map U) xi * charFun (PM.map V) (-xi) := by
  let F (u : ℝ) := Complex.exp ((xi : ℂ) * (u : ℂ) * Complex.I)
  let G (v : ℝ) := Complex.exp (((-xi : ℝ) : ℂ) * (v : ℂ) * Complex.I)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hG : Measurable G := by dsimp [G]; fun_prop
  have hsub : Measurable (fun z : OmegaP × OmegaM => U z.1 - V z.2) :=
    (hU.comp measurable_fst).sub (hV.comp measurable_snd)
  simp only [charFun_apply_real]
  rw [integral_map hsub.aemeasurable hF.aestronglyMeasurable,
    integral_map hU.aemeasurable hF.aestronglyMeasurable,
    integral_map hV.aemeasurable hG.aestronglyMeasurable]
  change (∫ z, F (U z.1 - V z.2) ∂(PP.prod PM)) =
    (∫ w, F (U w) ∂PP) * (∫ w, G (V w) ∂PM)
  have h : (fun z : OmegaP × OmegaM => F (U z.1 - V z.2)) =
      fun z => F (U z.1) * G (V z.2) := by
    funext z
    dsimp [F, G]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h]
  exact integral_prod_mul (fun w => F (U w)) (fun w => G (V w))
