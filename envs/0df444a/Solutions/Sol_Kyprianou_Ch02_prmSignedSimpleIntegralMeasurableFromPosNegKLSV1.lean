-- Prove2me | solution 1 for Kyprianou.Ch02.prmSignedSimpleIntegralMeasurableFromPosNegKLSV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:28:29.237747+00:00
-- url     : https://prove2.me/submissions/17c567d0-6616-4fbb-bd57-9c6e21b10bed

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_integrableSimpleMarkIffLintegralPartsFiniteV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R)
    (f : SimpleFunc ℝ ℝ)
    (hp : Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)] (fun ω => ∫⁻ z, R.indicator
        (fun z : ℝ × ℝ => ENNReal.ofReal (f z.2)) z ∂(N.N ω)))
    (hn : Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)] (fun ω => ∫⁻ z, R.indicator
        (fun z : ℝ × ℝ => ENNReal.ofReal (-(f z.2))) z ∂(N.N ω))) :
    Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)]
      (fun ω => ∫ z in R, (f z.2) ∂(N.N ω)) := by
  let a : Ω → ℝ≥0∞ := fun ω => ∫⁻ z in R, ENNReal.ofReal (f z.2) ∂(N.N ω)
  let b : Ω → ℝ≥0∞ := fun ω => ∫⁻ z in R, ENNReal.ofReal (-(f z.2)) ∂(N.N ω)
  have ha : Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
      MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)] a := by
    simpa only [a, lintegral_indicator hRm] using hp
  have hb : Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
      MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)] b := by
    simpa only [b, lintegral_indicator hRm] using hn
  have hiff (ω : Ω) :=
    Kyprianou.Ch02.integrableSimpleMarkIffLintegralPartsFiniteV1
      (N.N ω) R hRm f
  have hset : MeasurableSet[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)]
        {ω | a ω ≠ ⊤ ∧ b ω ≠ ⊤} := by
    have hlt : MeasurableSet[(⨆ C ∈
          {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)]
          {ω | a ω < ⊤ ∧ b ω < ⊤} :=
      (measurableSet_lt ha measurable_const).inter
        (measurableSet_lt hb measurable_const)
    simpa only [lt_top_iff_ne_top] using hlt
  have hrep (ω : Ω) :
      (∫ z in R, (f z.2) ∂(N.N ω)) =
        if a ω ≠ ⊤ ∧ b ω ≠ ⊤ then (a ω).toReal - (b ω).toReal else 0 := by
    by_cases hi : Integrable (fun z : ℝ × ℝ => (f z.2)) ((N.N ω).restrict R)
    · rw [if_pos ((hiff ω).mp hi)]
      simpa only [a, b, lintegral_indicator hRm] using
        (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi)
    · rw [if_neg (fun h => hi ((hiff ω).mpr h))]
      exact integral_undef hi
  have hfinal : Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)]
      (fun ω => if a ω ≠ ⊤ ∧ b ω ≠ ⊤ then (a ω).toReal - (b ω).toReal else 0) :=
    (ha.ennreal_toReal.sub hb.ennreal_toReal).ite hset measurable_const
  convert hfinal using 1
  exact funext hrep
