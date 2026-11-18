-- Prove2me | solution 1 for Kyprianou.Ch01.mapRestrictedIndependentProduct
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T03:05:46.327359+00:00
-- url     : https://prove2.me/submissions/9acd82c8-4e87-421c-9347-6d6876599f4c

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Map
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → α) (g : Ω → β)
    (hf : Measurable f) (hg : Measurable g)
    (hind : IndepFun f g P)
    (A : Set α) (hA : MeasurableSet A) :
    Measure.map (fun ω => (f ω, g ω))
      (P.restrict (f ⁻¹' A)) =
      (Measure.map f (P.restrict (f ⁻¹' A))).prod
        (Measure.map g P) := by
  have hfg : Measurable (fun ω => (f ω, g ω)) := hf.prodMk hg
  haveI : IsFiniteMeasure (Measure.map f (P.restrict (f ⁻¹' A))) := inferInstance
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply hfg (hs.prod ht), Measure.map_apply hf hs, Measure.map_apply hg ht,
    Measure.restrict_apply (hfg (hs.prod ht)), Measure.restrict_apply (hf hs)]
  have h1 : (fun ω => (f ω, g ω)) ⁻¹' (s ×ˢ t) ∩ f ⁻¹' A = f ⁻¹' (s ∩ A) ∩ g ⁻¹' t := by
    ext ω; simp [and_comm, and_assoc, and_left_comm]
  have h2 : f ⁻¹' s ∩ f ⁻¹' A = f ⁻¹' (s ∩ A) := rfl
  rw [h1, h2]
  exact hind.measure_inter_preimage_eq_mul _ _ (hs.inter hA) ht
