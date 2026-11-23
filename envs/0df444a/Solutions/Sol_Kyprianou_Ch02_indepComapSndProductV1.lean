-- Prove2me | solution 1 for Kyprianou.Ch02.indepComapSndProductV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:40:47.725308+00:00
-- url     : https://prove2.me/submissions/898bc018-5593-40b8-bca5-88279e587c97

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
    {n₁ n₂ : MeasurableSpace Ω₂} (h : Indep n₁ n₂ P₂) :
    Indep (n₁.comap (Prod.snd : Ω₁ × Ω₂ → Ω₂))
      (n₂.comap (Prod.snd : Ω₁ × Ω₂ → Ω₂)) (@Measure.prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂) := by
  rw [Indep_iff] at h ⊢
  intro s t hs ht
  rcases hs with ⟨s', hs', rfl⟩
  rcases ht with ⟨t', ht', rfl⟩
  have h1 : (Prod.snd : Ω₁ × Ω₂ → Ω₂) ⁻¹' s' = (Set.univ : Set Ω₁) ×ˢ s' := by
    ext ⟨a, b⟩; simp
  have h2 : (Prod.snd : Ω₁ × Ω₂ → Ω₂) ⁻¹' t' = (Set.univ : Set Ω₁) ×ˢ t' := by
    ext ⟨a, b⟩; simp
  have h12 : ((Prod.snd : Ω₁ × Ω₂ → Ω₂) ⁻¹' s') ∩ ((Prod.snd : Ω₁ × Ω₂ → Ω₂) ⁻¹' t') =
      (Set.univ : Set Ω₁) ×ˢ (s' ∩ t') := by
    ext ⟨a, b⟩; simp
  rw [h12, h1, h2, @Measure.prod_prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂ _,
    @Measure.prod_prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂ _,
    @Measure.prod_prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂ _,
    measure_univ, one_mul, one_mul, one_mul, h s' t' hs' ht']
