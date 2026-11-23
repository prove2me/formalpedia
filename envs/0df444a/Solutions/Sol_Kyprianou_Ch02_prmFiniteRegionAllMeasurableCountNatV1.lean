-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteRegionAllMeasurableCountNatV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:50:04.821038+00:00
-- url     : https://prove2.me/submissions/f3b1221d-1985-4299-922a-1801af416d6f

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F002
import Theorems.Thm_LevyStochCalc_Probability_isIntegerValued_of_isPiSystem
import Theorems.Thm_LevyStochCalc_Probability_isPiSystem_finInters

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R)
    (hRfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ A : Set (ℝ × ℝ),
      MeasurableSet A → ∃ n : ℕ, N.N ω (A ∩ R) = n := by
  let C : Set (Set (ℝ × ℝ)) :=
    LevyStochCalc.Probability.finInters
      (MeasurableSpace.natGeneratingSequence (ℝ × ℝ))
  have hcount : C.Countable :=
    LevyStochCalc.Probability.countable_finInters _
  have hmeas : ∀ A ∈ C, MeasurableSet A :=
    LevyStochCalc.Probability.measurableSet_of_mem_finInters
      (MeasurableSpace.measurableSet_natGeneratingSequence)
  have hgen : (inferInstance : MeasurableSpace (ℝ × ℝ)) =
      MeasurableSpace.generateFrom C := by
    change (inferInstance : MeasurableSpace (ℝ × ℝ)) =
      MeasurableSpace.generateFrom
        (LevyStochCalc.Probability.finInters
          (MeasurableSpace.natGeneratingSequence (ℝ × ℝ)))
    rw [LevyStochCalc.Probability.generateFrom_finInters,
      MeasurableSpace.generateFrom_natGeneratingSequence]
  have hpi : IsPiSystem C :=
    LevyStochCalc.Probability.isPiSystem_finInters _
  have hpiece : ∀ A ∈ C, ∀ᵐ ω ∂P, ∃ n : ℕ, N.N ω (A ∩ R) = n := by
    intro A hA
    exact N.integer_valued ((hmeas A hA).inter hRm)
      (ne_top_of_le_ne_top hRfin (measure_mono Set.inter_subset_right))
  have hall : ∀ᵐ ω ∂P, ∀ A ∈ C, ∃ n : ℕ, N.N ω (A ∩ R) = n :=
    (ae_ball_iff hcount).2 hpiece
  filter_upwards [hall, N.integer_valued hRm hRfin] with ω hω hR
  obtain ⟨k, hk⟩ := hR
  haveI : IsFiniteMeasure ((N.N ω).restrict R) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hk]
    exact ENNReal.natCast_lt_top k
  have hC : ∀ A ∈ C, ∃ n : ℕ, ((N.N ω).restrict R) A = n := by
    intro A hA
    rw [Measure.restrict_apply (hmeas A hA)]
    exact hω A hA
  have huniv : ∃ k : ℕ, ((N.N ω).restrict R) Set.univ = k := by
    refine ⟨k, ?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hk
  have htrue :=
    LevyStochCalc.Probability.isIntegerValued_of_isPiSystem
      hgen hpi hC huniv
  intro A hA
  have hAint := htrue A hA
  rw [Measure.restrict_apply hA] at hAint
  exact hAint
