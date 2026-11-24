-- Prove2me | solution 1 for Kyprianou.Ch02.productNormalisedBrownianPoissonIndependentV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:44:48.352136+00:00
-- url     : https://prove2.me/submissions/0df54c70-d790-47fe-93ea-33e954876122

import Theorems.Thm_Kyprianou_Ch02_brownianProductFstV1
import Theorems.Thm_Kyprianou_Ch02_poissonRandomMeasureProductSndV1
import Theorems.Thm_Kyprianou_Ch02_indepFunSeparateProductCoordinatesV1
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou Kyprianou.Ch02
theorem solution
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (ν : Measure ℝ) [SigmaFinite ν]
    (B₁ : LevyStochCalc.Brownian.BrownianMotion P₁)
    (N₂ : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P₂ ν)
    (hB₁zero : ∀ ω : Ω₁, B₁.W 0 ω = 0) :
    ∃ (B : LevyStochCalc.Brownian.BrownianMotion (P₁.prod P₂))
      (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} (P₁.prod P₂) ν),
      ProbabilityTheory.IndepFun
        (fun ω => fun (t : ℝ) => B.W t ω)
        (fun ω => N.N ω) (P₁.prod P₂) ∧
      (∀ ω : Ω₁ × Ω₂, B.W 0 ω = 0) := by
  obtain ⟨B, hB⟩ :=
    Kyprianou.Ch02.brownianProductFstV1 P₁ P₂ B₁
  obtain ⟨N, hN⟩ :=
    Kyprianou.Ch02.poissonRandomMeasureProductSndV1 P₁ P₂ ν N₂
  have hIndep := Kyprianou.Ch02.indepFunSeparateProductCoordinatesV1
    P₁ P₂ (fun ω₁ => fun (t : ℝ) => B₁.W t ω₁) (fun ω₂ => N₂.N ω₂)
  have hpath : (fun ω => fun (t : ℝ) => B.W t ω) =
      (fun ω : Ω₁ × Ω₂ => fun (t : ℝ) => B₁.W t ω.1) := by
    funext ω t
    exact hB t ω
  have hmeasure : (fun ω => N.N ω) =
      (fun ω : Ω₁ × Ω₂ => N₂.N ω.2) := by
    funext ω
    exact hN ω
  refine ⟨B, N, ?_, ?_⟩
  · simpa only [hpath, hmeasure] using hIndep
  · intro ω
    rw [hB 0 ω]
    exact hB₁zero ω.1


