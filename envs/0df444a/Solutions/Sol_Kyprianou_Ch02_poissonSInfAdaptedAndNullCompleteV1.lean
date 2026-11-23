-- Prove2me | solution 1 for Kyprianou.Ch02.poissonSInfAdaptedAndNullCompleteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:45:55.400245+00:00
-- url     : https://prove2.me/submissions/4e700ea7-6fd7-4bf4-9699-de74b0c5d1ee

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (S : Set (Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)))
    (hS : ∀ G : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω),
      G ∈ S → (∀ t u : ℝ≥0, u ≤ t → ∀ A : Set ℝ, MeasurableSet A →
      @Measurable Ω ℝ≥0∞ (G t) inferInstance
        (fun ω => N.N ω (Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ A))) ∧
        (∀ t (U : Set Ω), MeasurableSet U → P U = 0 →
      @MeasurableSet Ω (G t) U) ∧ G.IsRightContinuous) :
    (∀ t u : ℝ≥0, u ≤ t → ∀ A : Set ℝ, MeasurableSet A →
      @Measurable Ω ℝ≥0∞ ((sInf S) t) inferInstance
        (fun ω => N.N ω (Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ A))) ∧
    (∀ t (U : Set Ω), MeasurableSet U → P U = 0 →
      @MeasurableSet Ω ((sInf S) t) U) := by
  classical
  constructor
  · intro t u htu A hA
    change ∀ V : Set ℝ≥0∞, MeasurableSet V →
      @MeasurableSet Ω ((sInf S) t)
        ((fun ω => N.N ω (Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ A)) ⁻¹' V)
    intro V hV
    by_cases hs : S.Nonempty
    · have hFilt : ((sInf S) : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) t =
          sInf ((fun (G : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) => G t) '' S) := by
        simp [Filtration.sInf_def, hs]
      rw [hFilt]
      apply MeasurableSpace.measurableSet_sInf.mpr
      intro m hm
      rcases hm with ⟨G, hG, rfl⟩
      exact ((hS G hG).1 t u htu A hA) hV
    · have hFilt : ((sInf S) : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) t =
          (inferInstance : MeasurableSpace Ω) := by
        simp [Filtration.sInf_def, hs]
      rw [hFilt]
      exact (N.measurable_eval (measurableSet_Ioc.prod hA)) hV
  · intro t U hU hPU
    by_cases hs : S.Nonempty
    · have hFilt : ((sInf S) : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) t =
          sInf ((fun (G : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) => G t) '' S) := by
        simp [Filtration.sInf_def, hs]
      rw [hFilt]
      apply MeasurableSpace.measurableSet_sInf.mpr
      intro m hm
      rcases hm with ⟨G, hG, rfl⟩
      exact (hS G hG).2.1 t U hU hPU
    · have hFilt : ((sInf S) : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) t =
          (inferInstance : MeasurableSpace Ω) := by
        simp [Filtration.sInf_def, hs]
      rw [hFilt]
      exact hU
