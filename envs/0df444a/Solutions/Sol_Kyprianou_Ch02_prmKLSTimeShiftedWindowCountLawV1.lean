-- Prove2me | solution 1 for Kyprianou.Ch02.prmKLSTimeShiftedWindowCountLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:14:05.342811+00:00
-- url     : https://prove2.me/submissions/cf772c43-1017-4101-b8ac-a99ceb38b212

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (C : Set ℝ) (hC : MeasurableSet C) (hfinite : ν C < ⊤) :
    ∀ s t : ℝ≥0,
      P.map (fun (ω : Ω) =>
        N.N ω (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ C)) =
      P.map (fun (ω : Ω) =>
        N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ C)) := by
  intro s t
  let R : Set (ℝ × ℝ) := Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ C
  let R₀ : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ C
  have hs : (0 : ℝ) ≤ (s : ℝ) := NNReal.coe_nonneg s
  have hstrip (u : ℝ≥0) :
      LevyStochCalc.Poisson.referenceIntensity ν
        (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ) ×ˢ C) =
        ENNReal.ofReal (t : ℝ) * ν C := by
    have hu : (0 : ℝ) ≤ (u : ℝ) := NNReal.coe_nonneg u
    rw [LevyStochCalc.Poisson.referenceIntensity,
      Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc,
      Set.inter_eq_self_of_subset_left
        (show Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ) ⊆ Set.Ici 0 from
          fun x hx => hu.trans hx.1.le),
      Real.volume_Ioc]
    congr 1
    push_cast
    ring
  have hR : LevyStochCalc.Poisson.referenceIntensity ν R =
      ENNReal.ofReal (t : ℝ) * ν C := by
    simpa only [R] using hstrip s
  have hzero : LevyStochCalc.Poisson.referenceIntensity ν R₀ =
      ENNReal.ofReal (t : ℝ) * ν C := by
    simpa [R₀] using hstrip 0
  have hfinR : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤ := by
    rw [hR]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.ne
  have hfin0 : LevyStochCalc.Poisson.referenceIntensity ν R₀ ≠ ⊤ := by
    rw [hzero]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.ne
  calc
    P.map (fun ω => N.N ω R) =
        LevyStochCalc.Poisson.poissonMeasureENN
          (LevyStochCalc.Poisson.referenceIntensity ν R).toNNReal :=
      N.poisson_law (measurableSet_Ioc.prod hC) hfinR
    _ = LevyStochCalc.Poisson.poissonMeasureENN
          (LevyStochCalc.Poisson.referenceIntensity ν R₀).toNNReal := by
      rw [hR, hzero]
    _ = P.map (fun ω => N.N ω R₀) :=
      (N.poisson_law (measurableSet_Ioc.prod hC) hfin0).symm
