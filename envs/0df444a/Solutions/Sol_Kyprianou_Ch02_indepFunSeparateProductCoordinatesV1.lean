-- Prove2me | solution 1 for Kyprianou.Ch02.indepFunSeparateProductCoordinatesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:40:52.387893+00:00
-- url     : https://prove2.me/submissions/482dac43-5c13-4dd1-8f23-3c833baa5c85

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib.Probability.Independence.Basic
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_exists_readable
import Theorems.Thm_Kyprianou_poissonRandomMeasureExists

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

set_option autoImplicit false

theorem solution
    {Ω₁ Ω₂ β γ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace β] [MeasurableSpace γ]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (f : Ω₁ → β) (g : Ω₂ → γ) :
    IndepFun (fun ω : Ω₁ × Ω₂ => f ω.1) (fun ω : Ω₁ × Ω₂ => g ω.2) (P₁.prod P₂) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  have h1 : (fun ω : Ω₁ × Ω₂ => f ω.1) ⁻¹' s = (f ⁻¹' s) ×ˢ (Set.univ : Set Ω₂) := by
    ext ⟨a, b⟩; simp
  have h2 : (fun ω : Ω₁ × Ω₂ => g ω.2) ⁻¹' t = (Set.univ : Set Ω₁) ×ˢ (g ⁻¹' t) := by
    ext ⟨a, b⟩; simp
  have h12 : ((fun ω : Ω₁ × Ω₂ => f ω.1) ⁻¹' s) ∩ ((fun ω : Ω₁ × Ω₂ => g ω.2) ⁻¹' t) =
      (f ⁻¹' s) ×ˢ (g ⁻¹' t) := by
    ext ⟨a, b⟩; simp
  rw [h12, h1, h2, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    measure_univ, measure_univ, mul_one, one_mul]
