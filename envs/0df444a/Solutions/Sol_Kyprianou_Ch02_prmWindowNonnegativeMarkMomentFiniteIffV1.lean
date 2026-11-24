-- Prove2me | solution 1 for Kyprianou.Ch02.prmWindowNonnegativeMarkMomentFiniteIffV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:32:12.694803+00:00
-- url     : https://prove2.me/submissions/fe77859a-373d-4cfc-9c25-122ed7884a39

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_lintegral_nat_count
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (f : ℝ → ℝ) (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (t : ℝ≥0) (ht : 0 < t) :
    ((∫⁻ ω, ∫⁻ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ),
          ENNReal.ofReal (f z.2) ∂(N.N ω) ∂P) < ⊤ ↔
      Integrable f ν) := by
  let R : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ
  let M : Ω → Measure (ℝ × ℝ) := fun ω => (N.N ω).restrict R
  have hR : MeasurableSet R := measurableSet_Ioc.prod MeasurableSet.univ
  have hm : Measurable M := Measure.measurable_of_measurable_coe M fun s hs => by
    simpa only [M, Measure.restrict_apply hs] using N.measurable_eval (hs.inter hR)
  have hb : P.bind M = (LevyStochCalc.Poisson.referenceIntensity ν).restrict R := by
    ext s hs
    rw [Measure.bind_apply hs hm.aemeasurable, Measure.restrict_apply hs]
    simp only [M, Measure.restrict_apply hs]
    by_cases h : LevyStochCalc.Poisson.referenceIntensity ν (s ∩ R) = ⊤
    · rw [h, lintegral_congr_ae (N.infinite_at_infinite_intensity (hs.inter hR) h)]
      simp
    · have hmeas := N.measurable_eval (hs.inter hR)
      have hc : Measurable (fun n : ℕ => (n : ℝ≥0∞)) := measurable_of_countable _
      have h1 : ∫⁻ ω, N.N ω (s ∩ R) ∂P =
          ∫⁻ x, x ∂(P.map (fun ω => N.N ω (s ∩ R))) :=
        (lintegral_map measurable_id hmeas).symm
      rw [h1, N.poisson_law (hs.inter hR) h,
        LevyStochCalc.Poisson.poissonMeasureENN,
        lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id hc,
        Kyprianou.ProofPreparation.poisson_lintegral_nat_count, ENNReal.coe_toNNReal h]
  have hprod : (LevyStochCalc.Poisson.referenceIntensity ν).restrict R =
      (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))).prod ν := by
    unfold LevyStochCalc.Poisson.referenceIntensity R
    rw [← Measure.restrict_prod_eq_prod_univ, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.mpr (fun x hx => hx.1.le)]
  have hme : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (f z.2)) :=
    ENNReal.measurable_ofReal.comp (hf.comp measurable_snd)
  change (∫⁻ ω, ∫⁻ z, ENNReal.ofReal (f z.2) ∂M ω ∂P) < ⊤ ↔ _
  rw [← Measure.lintegral_bind hm.aemeasurable hme.aemeasurable, hb, hprod,
    lintegral_prod _ hme.aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  have ht0 : ENNReal.ofReal (t : ℝ) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by exact_mod_cast ht)).ne'
  constructor
  · intro h
    refine ⟨hf.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).2 ?_⟩
    exact ENNReal.lt_top_of_mul_ne_top_left h.ne ht0
  · intro h
    exact ENNReal.mul_lt_top
      ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).1 h.2)
      ENNReal.ofReal_lt_top
