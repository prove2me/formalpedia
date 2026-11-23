-- Prove2me | solution 1 for Kyprianou.Ch02.indepComapFstProductV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:40:42.312737+00:00
-- url     : https://prove2.me/submissions/147f0388-74a9-4064-a7f7-f99bd6ae8f9f

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
    {Ω₁ Ω₂ : Type*} [mΩ₁ : MeasurableSpace Ω₁] [mΩ₂ : MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    {n₁ n₂ : MeasurableSpace Ω₁} (h : Indep n₁ n₂ P₁) :
    Indep (n₁.comap (Prod.fst : Ω₁ × Ω₂ → Ω₁))
      (n₂.comap (Prod.fst : Ω₁ × Ω₂ → Ω₁)) (@Measure.prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂) := by
  rw [Indep_iff] at h ⊢
  intro s t hs ht
  rcases hs with ⟨s', hs', rfl⟩
  rcases ht with ⟨t', ht', rfl⟩
  have h1 : (Prod.fst : Ω₁ × Ω₂ → Ω₁) ⁻¹' s' = s' ×ˢ (Set.univ : Set Ω₂) := by
    ext ⟨a, b⟩; simp
  have h2 : (Prod.fst : Ω₁ × Ω₂ → Ω₁) ⁻¹' t' = t' ×ˢ (Set.univ : Set Ω₂) := by
    ext ⟨a, b⟩; simp
  have h12 : ((Prod.fst : Ω₁ × Ω₂ → Ω₁) ⁻¹' s') ∩ ((Prod.fst : Ω₁ × Ω₂ → Ω₁) ⁻¹' t') =
      (s' ∩ t') ×ˢ (Set.univ : Set Ω₂) := by
    ext ⟨a, b⟩; simp
  rw [h12, h1, h2, @Measure.prod_prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂ _,
    @Measure.prod_prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂ _,
    @Measure.prod_prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂ _,
    measure_univ, mul_one, mul_one, mul_one, h s' t' hs' ht']
