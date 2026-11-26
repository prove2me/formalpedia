-- Prove2me | solution 1 for Kyprianou.Ch04.antitoneRewardMeanProperties
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:42:34.350326+00:00
-- url     : https://prove2.me/submissions/2451b73f-4187-417f-a4f7-f58e5e6db507

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Integrals of bounded decreasing jointly measurable rewards have a finite limit. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : NNReal × Ω → ℝ) (hm : Measurable g)
    (h0 : ∀ z, 0 ≤ g z) (h1 : ∀ z, g z ≤ 1)
    (ha : ∀ w, Antitone (fun t : NNReal => g (t,w))) :
    let f : NNReal → ℝ := fun t => ∫ w, g (t,w) ∂P
    Measurable f ∧ Antitone f ∧ (∀ t, 0 ≤ f t) ∧ (∀ t, f t ≤ 1) ∧
      ∃ ell : ℝ, (∀ t, ell ≤ f t) ∧ Tendsto f atTop (nhds ell) := by
  intro f
  have hc : StronglyMeasurable (Function.uncurry (fun (t : NNReal) (w : Ω) => g (t,w))) :=
    hm.stronglyMeasurable
  have hf : Measurable f := hc.integral_prod_right.measurable
  have hi (t : NNReal) : Integrable (fun w => g (t,w)) P :=
    (integrable_const (1 : ℝ)).mono (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 _), Real.norm_eq_abs, abs_one]
        exact h1 _)
  have hanti : Antitone f := fun t u htu => integral_mono (hi u) (hi t) (fun w => ha w htu)
  have hlo (t : NNReal) : 0 ≤ f t := integral_nonneg (fun w => h0 _)
  have hhi (t : NNReal) : f t ≤ 1 := by
    have h := integral_mono (hi t) (integrable_const (1 : ℝ)) (fun w => h1 (t,w))
    simpa using h
  have hb : BddBelow (range f) := ⟨0, by rintro x ⟨t,rfl⟩; exact hlo t⟩
  exact ⟨hf,hanti,hlo,hhi,⟨⨅ t, f t, fun t => ciInf_le hb t, tendsto_atTop_ciInf hanti hb⟩⟩
