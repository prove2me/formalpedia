-- Prove2me | solution 1 for ManyServerQED.Scheduling.brownian_weighted_finite_observation_law
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:33:44.593871+00:00
-- url     : https://prove2.me/submissions/459ebeaf-fb91-4b51-a3e2-b000cf9d79a1

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The finite-dimensional laws of a pre-Brownian motion are independent of
the realization, including repeated observation times and deterministic weights. -/
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ω' → ℝ}
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P')
    {m : ℕ} (t : Fin m → ℝ≥0) (c : Fin m → ℝ) :
    IdentDistrib (fun ω i => c i * B (t i) ω) (fun ω i => c i * C (t i) ω) P P' := by
  let I : Finset ℝ≥0 := Finset.univ.image t
  let p : Fin m → I := fun i => ⟨t i, Finset.mem_image.2 ⟨i,Finset.mem_univ _,rfl⟩⟩
  let f (x : I → ℝ) (i : Fin m) := c i * x (p i)
  have hf : Measurable f := measurable_pi_lambda _ fun i => (measurable_pi_apply (p i)).const_mul _
  have h1 := hB.hasLaw I
  have h2 := hC.hasLaw I
  exact (show IdentDistrib (fun ω => I.restrict (B · ω)) (fun ω => I.restrict (C · ω)) P P'
    from ⟨h1.aemeasurable,h2.aemeasurable,h1.map_eq.trans h2.map_eq.symm⟩).comp hf
