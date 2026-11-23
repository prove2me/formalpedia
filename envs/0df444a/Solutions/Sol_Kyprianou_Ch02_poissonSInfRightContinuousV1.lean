-- Prove2me | solution 1 for Kyprianou.Ch02.poissonSInfRightContinuousV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:39:37.19712+00:00
-- url     : https://prove2.me/submissions/3d111e73-cb90-4a12-ae58-4dc3f760b93e

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
    (sInf S).IsRightContinuous := by
  classical
  have hmono : ∀ F G : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω),
      F ≤ G → F.rightCont ≤ G.rightCont := by
    intro F G hFG t
    simp only [Filtration.rightCont_apply]
    split_ifs <;> first
      | exact iInf_mono (fun j => iInf_mono (fun hj => hFG j))
      | exact hFG t
  refine ⟨?_⟩
  apply le_sInf
  intro G hG
  haveI : G.IsRightContinuous := (hS G hG).2.2
  exact (hmono (sInf S) G (sInf_le hG)).trans
    (Filtration.IsRightContinuous.RC)
