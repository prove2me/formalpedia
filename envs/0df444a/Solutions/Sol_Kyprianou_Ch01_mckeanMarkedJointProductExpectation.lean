-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanMarkedJointProductExpectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:06:18.340144+00:00
-- url     : https://prove2.me/submissions/3677f7c5-2b64-4601-8aba-a6b14b464420

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ × Bool) (Z : Ω → ℝ)
    (g : (ℝ × Bool) × ℝ → ℝ) (K : ℝ)
    (hT : Measurable T) (hZ : Measurable Z)
    (hg : Measurable g) (hBound : ∀ p, ‖g p‖ ≤ K)
    (hInd : IndepFun T Z P) :
    (∫ ω, g (T ω, Z ω) ∂P) =
      (∫ a, ∫ z, g (a, z) ∂P.map Z ∂P.map T) := by
  have hLaw :
      P.map (fun ω => (T ω, Z ω)) = (P.map T).prod (P.map Z) :=
    (indepFun_iff_map_prod_eq_prod_map_map
      hT.aemeasurable hZ.aemeasurable).1 hInd
  haveI : IsProbabilityMeasure (P.map T) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  haveI : IsProbabilityMeasure (P.map Z) :=
    Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hgInt : Integrable g ((P.map T).prod (P.map Z)) :=
    Integrable.of_bound hg.aestronglyMeasurable K
      (Filter.Eventually.of_forall hBound)
  calc
    (∫ ω, g (T ω, Z ω) ∂P)
        = ∫ p, g p ∂P.map (fun ω => (T ω, Z ω)) :=
      (integral_map (hT.prodMk hZ).aemeasurable
        hg.aestronglyMeasurable).symm
    _ = ∫ p, g p ∂((P.map T).prod (P.map Z)) := by rw [hLaw]
    _ = ∫ a, ∫ z, g (a, z) ∂P.map Z ∂P.map T :=
      integral_prod g hgInt
