-- Prove2me | solution 1 for Kyprianou.Ch04.boundedClockProductAverage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:36:38.959614+00:00
-- url     : https://prove2.me/submissions/ecd20c97-fbba-4991-a62b-2b601e6a180a

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Disintegrate a bounded measurable clock reward on a product space. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (g : NNReal × Ω → ℝ) (hm : Measurable g)
    (h0 : ∀ z, 0 ≤ g z) (h1 : ∀ z, g z ≤ 1) :
    (∫ z : Ω × ℝ, g (z.2.toNNReal, z.1) ∂(P.prod Q)) =
      ∫ t : NNReal, (∫ w : Ω, g (t,w) ∂P) ∂(Q.map Real.toNNReal) := by
  let G : Ω × ℝ → ℝ := fun z => g (z.2.toNNReal, z.1)
  have hG : Measurable G := hm.comp (by fun_prop)
  have hi : Integrable G (P.prod Q) :=
    (integrable_const (1 : ℝ)).mono hG.aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 _), Real.norm_eq_abs, abs_one]
        exact h1 _)
  let f : NNReal → ℝ := fun t => ∫ w : Ω, g (t,w) ∂P
  have hc : StronglyMeasurable (Function.uncurry (fun (t : NNReal) (w : Ω) => g (t,w))) :=
    hm.stronglyMeasurable
  have hf : Measurable f := hc.integral_prod_right.measurable
  calc
    _ = ∫ r : ℝ, f r.toNNReal ∂Q := integral_prod_symm G hi
    _ = _ := (integral_map (by fun_prop : Measurable Real.toNNReal).aemeasurable
      hf.aestronglyMeasurable).symm
