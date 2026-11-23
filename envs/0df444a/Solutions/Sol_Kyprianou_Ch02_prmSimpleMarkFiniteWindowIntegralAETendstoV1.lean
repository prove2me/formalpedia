-- Prove2me | solution 1 for Kyprianou.Ch02.prmSimpleMarkFiniteWindowIntegralAETendstoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:18:55.535952+00:00
-- url     : https://prove2.me/submissions/c84c4c36-748c-4d2d-9c47-99ed50d7f10e

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmFiniteIntensityWindowSimpleMarkIntegralTendstoV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkTimeRectIntensityFiniteV1

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Both windows have finite intensity and a common full-measure approximation event. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hf : ∀ x : ℝ, Tendsto (fun n => f n x) atTop (𝓝 x))
    (s t : ℝ≥0) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => ∫ z in
        (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
        f n z.2 ∂(N.N ω)) atTop
        (𝓝 (∫ z in
          (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
          z.2 ∂(N.N ω))) ∧
      Tendsto (fun n => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        f n z.2 ∂(N.N ω)) atTop
        (𝓝 (∫ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          z.2 ∂(N.N ω))) := by
  have hs :=
    Kyprianou.Ch02.prmFiniteIntensityWindowSimpleMarkIntegralTendstoV1
      P ν N _ (measurableSet_Ioc.prod hB)
      (Kyprianou.Ch02.prmFiniteMarkTimeRectIntensityFiniteV1
        ν B hB hfinite s (s + t)) f hf
  have ht :=
    Kyprianou.Ch02.prmFiniteIntensityWindowSimpleMarkIntegralTendstoV1
      P ν N _ (measurableSet_Ioc.prod hB)
      (Kyprianou.Ch02.prmFiniteMarkTimeRectIntensityFiniteV1
        ν B hB hfinite 0 t) f hf
  exact hs.and ht
