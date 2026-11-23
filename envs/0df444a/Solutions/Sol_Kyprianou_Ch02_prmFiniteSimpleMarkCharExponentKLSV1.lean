-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteSimpleMarkCharExponentKLSV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:12:14.325546+00:00
-- url     : https://prove2.me/submissions/76a50b79-dac6-45bd-82de-30caa7688e95

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkIntegralAEFibreSumKLSV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkTimeRectIntensityFiniteV1
import Theorems.Thm_Kyprianou_Ch02_prmKLSFiniteSimpleFibreWeightedCountCharV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleCharFibreIntegralV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- A finite-simple marked Poisson integral has the exponent of its mark-fibre counts. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ (f : SimpleFunc ℝ ℝ) (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), f z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * f x : ℝ) : ℂ))) - 1) ∂ν) := by
  intro f t ξ
  have hAE :=
    Kyprianou.Ch02.prmFiniteSimpleMarkIntegralAEFibreSumKLSV1
      P ν N (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)
      (measurableSet_Ioc.prod hB)
      (Kyprianou.Ch02.prmFiniteMarkTimeRectIntensityFiniteV1
        ν B hB hfinite 0 t) f
  have hset (x : ℝ) :
      ((Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) ∩
        {z : ℝ × ℝ | f z.2 = x}) =
      Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
        (B ∩ {y : ℝ | f y = x}) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_setOf_eq]
    tauto
  have hsum :
      (fun ω : Ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        f z.2 ∂(N.N ω)) =ᵐ[P]
      (fun ω : Ω => ∑ x ∈ f.range, x * (N.N ω
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
          (B ∩ {y : ℝ | f y = x}))).toReal) := by
    filter_upwards [hAE] with ω hω
    calc
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        f z.2 ∂(N.N ω)) =
          ∑ x ∈ f.range, (N.N ω
            ((Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) ∩
              {z : ℝ × ℝ | f z.2 = x})).toReal * x := hω
      _ = ∑ x ∈ f.range, x * (N.N ω
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
            (B ∩ {y : ℝ | f y = x}))).toReal := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hset]
        ring
  have hCount :=
    Kyprianou.Ch02.prmKLSFiniteSimpleFibreWeightedCountCharV1
      P ν N B hB hfinite f t ξ
  have hFibre :=
    Kyprianou.Ch02.prmFiniteSimpleCharFibreIntegralV1
      ν B hB hfinite f ξ
  calc
    charFun (P.map (fun ω => ∫ z in
      (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), f z.2 ∂(N.N ω))) ξ =
      charFun (P.map (fun ω : Ω =>
        ∑ x ∈ f.range, x * (N.N ω
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
            (B ∩ {y : ℝ | f y = x}))).toReal)) ξ := by
        rw [Measure.map_congr hsum]
    _ = Complex.exp ((((t : ℝ) : ℂ)) *
      ∑ x ∈ f.range, ((((ν (B ∩ {y : ℝ | f y = x})).toReal : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1))) := hCount
    _ = Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * f x : ℝ) : ℂ))) - 1) ∂ν) := by
      rw [hFibre]
