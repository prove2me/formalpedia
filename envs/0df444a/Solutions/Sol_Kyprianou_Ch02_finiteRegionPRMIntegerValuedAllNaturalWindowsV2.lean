-- Prove2me | solution 1 for Kyprianou.Ch02.finiteRegionPRMIntegerValuedAllNaturalWindowsV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:25:54.484095+00:00
-- url     : https://prove2.me/submissions/6b6b2b7b-dbfb-40aa-8340-62d309e5d94b

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
import Theorems.Thm_LevyStochCalc_Probability_isIntegerValued_of_isPiSystem
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℕ,
      LevyStochCalc.Probability.IsIntegerValued
        ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B)) := by
  classical
  apply ae_all_iff.mpr
  intro T
  let R : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B
  have hRm : MeasurableSet R := measurableSet_Ioc.prod hB
  have hRfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤ :=
    LevyStochCalc.Poisson.referenceIntensity_Ioc_prod_ne_top
      hfinite.ne (T : ℝ)
  have hcell : ∀ t : Finset ℕ,
      MeasurableSet
        (⋂ i ∈ t, MeasurableSpace.natGeneratingSequence (ℝ × ℝ) i) :=
    fun t => MeasurableSet.biInter t.countable_toSet
      fun i _ => MeasurableSpace.measurableSet_natGeneratingSequence i
  have hgen : ∀ t : Finset ℕ, ∀ᵐ ω ∂P, ∃ n : ℕ,
      N.N ω
        ((⋂ i ∈ t, MeasurableSpace.natGeneratingSequence (ℝ × ℝ) i) ∩ R)
        = n := by
    intro t
    refine N.integer_valued ((hcell t).inter hRm) ?_
    exact ne_top_of_le_ne_top hRfin (measure_mono Set.inter_subset_right)
  have huniv : ∀ᵐ ω ∂P, ∃ n : ℕ, N.N ω R = n :=
    N.integer_valued hRm hRfin
  filter_upwards [ae_all_iff.mpr hgen, huniv] with ω hω hωu
  have hmass : ∃ n : ℕ, ((N.N ω).restrict R) Set.univ = n := by
    obtain ⟨n, hn⟩ := hωu
    exact ⟨n, by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact hn⟩
  haveI : IsFiniteMeasure ((N.N ω).restrict R) := by
    obtain ⟨n, hn⟩ := hmass
    exact ⟨by rw [hn]; exact ENNReal.natCast_lt_top n⟩
  refine LevyStochCalc.Probability.isIntegerValued_of_isPiSystem
    (C := LevyStochCalc.Poisson.markPiSystem ℝ)
    (LevyStochCalc.Poisson.generateFrom_markPiSystem (E := ℝ)).symm
    (LevyStochCalc.Poisson.isPiSystem_markPiSystem (E := ℝ))
    ?_ hmass
  intro A hA
  obtain ⟨t, rfl⟩ := LevyStochCalc.Probability.mem_finInters_iff.mp hA
  obtain ⟨n, hn⟩ := hω t
  exact ⟨n, by rw [Measure.restrict_apply (hcell t)]; exact hn⟩
