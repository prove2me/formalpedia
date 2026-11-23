-- Prove2me | solution 1 for Kyprianou.Ch02.prmSimpleMarkWindowMeasurableAndSameLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:19:28.799969+00:00
-- url     : https://prove2.me/submissions/05e4e752-ecf4-47f9-bdc4-d64fbe74cb1e

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkIntegralMeasurableKLSV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkIntegralAEFibreSumKLSV1
import Theorems.Thm_Kyprianou_Ch02_prmSimpleMarkFibreCountWeightedShiftLawV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkTimeRectIntensityFiniteV1
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Transfer the finite simple count law to marked integrals on a.s. finite windows. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (f : SimpleFunc ℝ ℝ) (s t : ℝ≥0) :
    Measurable (fun (ω : Ω) =>
      ∫ z in (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
        f z.2 ∂(N.N ω)) ∧
    Measurable (fun (ω : Ω) =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        f z.2 ∂(N.N ω)) ∧
    P.map (fun (ω : Ω) =>
      ∫ z in (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
        f z.2 ∂(N.N ω)) =
    P.map (fun (ω : Ω) =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        f z.2 ∂(N.N ω)) := by
  have hM (a b : ℝ≥0) :
      Measurable (fun (ω : Ω) =>
        ∫ z in (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ B),
          f z.2 ∂(N.N ω)) :=
    Kyprianou.Ch02.prmFiniteSimpleMarkIntegralMeasurableKLSV1
      P ν N _ (measurableSet_Ioc.prod hB) f
  have hset (I : Set ℝ) (x : ℝ) :
      (I ×ˢ B) ∩ {z : ℝ × ℝ | f z.2 = x} =
        I ×ˢ (B ∩ {y : ℝ | f y = x}) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_setOf_eq]
    tauto
  have hAE (a b : ℝ≥0) :
      ∀ᵐ ω ∂P,
        (∫ z in (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ B),
          f z.2 ∂(N.N ω)) =
        ∑ x ∈ f.range, x * (N.N ω
          (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ
            (B ∩ {y : ℝ | f y = x}))).toReal := by
    have hw :=
      Kyprianou.Ch02.prmFiniteSimpleMarkIntegralAEFibreSumKLSV1
        P ν N _ (measurableSet_Ioc.prod hB)
        (Kyprianou.Ch02.prmFiniteMarkTimeRectIntensityFiniteV1
          ν B hB hfinite a b) f
    filter_upwards [hw] with ω hω
    calc
      (∫ z in (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ B),
          f z.2 ∂(N.N ω)) =
        ∑ x ∈ f.range, (N.N ω
          ((Set.Ioc (a : ℝ) (b : ℝ) ×ˢ B) ∩
            {z : ℝ × ℝ | f z.2 = x})).toReal * x := hω
      _ = ∑ x ∈ f.range, x * (N.N ω
          (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ
            (B ∩ {y : ℝ | f y = x}))).toReal := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hset]
        ring
  refine ⟨hM s (s + t), hM 0 t, ?_⟩
  calc
    P.map (fun (ω : Ω) =>
      ∫ z in (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
        f z.2 ∂(N.N ω)) =
      P.map (fun (ω : Ω) =>
        ∑ x ∈ f.range, x * (N.N ω
          (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ
            (B ∩ {y : ℝ | f y = x}))).toReal) :=
      Measure.map_congr (hAE s (s + t))
    _ = P.map (fun (ω : Ω) =>
        ∑ x ∈ f.range, x * (N.N ω
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
            (B ∩ {y : ℝ | f y = x}))).toReal) :=
      (Kyprianou.Ch02.prmSimpleMarkFibreCountWeightedShiftLawV1
        P ν N B hB hfinite f s t).2
    _ = P.map (fun (ω : Ω) =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        f z.2 ∂(N.N ω)) :=
      (Measure.map_congr (hAE 0 t)).symm
