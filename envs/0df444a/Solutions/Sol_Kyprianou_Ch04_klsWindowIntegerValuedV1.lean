-- Prove2me | solution 1 for Kyprianou.Ch04.klsWindowIntegerValuedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:11:09.758392+00:00
-- url     : https://prove2.me/submissions/dd9e88ef-337b-407a-a152-c1eef28dbe36

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_SourceProof_adf2db00933ba5955625daf4
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F002
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F003
import Theorems.Thm_LevyStochCalc_Probability_isIntegerValued_of_isPiSystem
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
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
  have hwindow (T : ℝ) : LevyStochCalc.Poisson.referenceIntensity ν
      (Set.Ioc (0 : ℝ) T ×ˢ B) ≠ ⊤ := by
    have hvalue : LevyStochCalc.Poisson.referenceIntensity ν
        (Set.Ioc (0 : ℝ) T ×ˢ B) = ENNReal.ofReal T * ν B := by
      rw [LevyStochCalc.Poisson.referenceIntensity, Measure.prod_prod,
        Measure.restrict_apply measurableSet_Ioc]
      congr 1
      have hset : Set.Ioc (0 : ℝ) T ∩ Set.Ici (0 : ℝ) =
          Set.Ioc (0 : ℝ) T := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici,
          and_iff_left_iff_imp]
        exact fun h => h.1.le
      rw [hset, Real.volume_Ioc, sub_zero]
    rw [hvalue]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.ne
  have hRfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤ :=
    hwindow T
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
  have : IsFiniteMeasure ((N.N ω).restrict R) := by
    obtain ⟨n, hn⟩ := hmass
    exact ⟨by rw [hn]; exact ENNReal.natCast_lt_top n⟩
  refine LevyStochCalc.Probability.isIntegerValued_of_isPiSystem
    (C := LevyStochCalc.Probability.finInters (MeasurableSpace.natGeneratingSequence (ℝ × ℝ)))
    (by rw [LevyStochCalc.Probability.generateFrom_finInters, MeasurableSpace.generateFrom_natGeneratingSequence])
    (Prove2MeSourceProof.h_adf2db00933ba5955625daf4 _)
    ?_ hmass
  intro A hA
  obtain ⟨t, rfl⟩ := LevyStochCalc.Probability.mem_finInters_iff.mp hA
  obtain ⟨n, hn⟩ := hω t
  exact ⟨n, by rw [Measure.restrict_apply (hcell t)]; exact hn⟩

