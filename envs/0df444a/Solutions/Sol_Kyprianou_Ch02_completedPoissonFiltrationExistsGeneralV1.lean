-- Prove2me | solution 1 for Kyprianou.Ch02.completedPoissonFiltrationExistsGeneralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:29:18.877802+00:00
-- url     : https://prove2.me/submissions/241c8a10-3100-4c3d-b6ee-2ed6c2b31c5a

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_poissonAdmissibleFiltrationSInfV1
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    : ∃ (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ := by
  classical
  let S : Set (Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) :=
    {G | ((∀ t u : ℝ≥0, u ≤ t → ∀ A : Set ℝ, MeasurableSet A →
      @Measurable Ω ℝ≥0∞ (G t) inferInstance
        (fun ω => N.N ω (Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ A)))) ∧ ((∀ t (U : Set Ω), MeasurableSet U → P U = 0 →
      @MeasurableSet Ω (G t) U)) ∧ G.IsRightContinuous}
  have hS : ∀ G : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω),
      G ∈ S → ((∀ t u : ℝ≥0, u ≤ t → ∀ A : Set ℝ, MeasurableSet A →
      @Measurable Ω ℝ≥0∞ (G t) inferInstance
        (fun ω => N.N ω (Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ A)))) ∧ ((∀ t (U : Set Ω), MeasurableSet U → P U = 0 →
      @MeasurableSet Ω (G t) U)) ∧ G.IsRightContinuous := by
    intro G hG
    exact hG
  obtain ⟨hcount, hnull, hrc⟩ :=
    Kyprianou.Ch02.poissonAdmissibleFiltrationSInfV1 P ν N S hS
  refine ⟨sInf S, hcount, hnull, hrc, ?_⟩
  intro G hGcount hGnull hGrc
  exact sInf_le (show G ∈ S from ⟨hGcount, hGnull, hGrc⟩)
