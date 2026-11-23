-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteRegionMarkedIntegrableAllTimesAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:38:18.488615+00:00
-- url     : https://prove2.me/submissions/9805484b-05ec-4e64-bf7d-507d9791fce5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmFiniteWindowDiracLawV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0), IntegrableOn (fun z : ℝ × ℝ => z.2)
      (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) (N.N ω) := by
  have hwindow (T : ℕ) : LevyStochCalc.Poisson.referenceIntensity ν
      (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) ≠ ⊤ := by
    have hvalue : LevyStochCalc.Poisson.referenceIntensity ν
        (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) =
        ENNReal.ofReal (T : ℝ) * ν B := by
      rw [LevyStochCalc.Poisson.referenceIntensity, Measure.prod_prod,
        Measure.restrict_apply measurableSet_Ioc]
      congr 1
      have hset : Set.Ioc (0 : ℝ) (T : ℝ) ∩ Set.Ici (0 : ℝ) =
          Set.Ioc (0 : ℝ) (T : ℝ) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici,
          and_iff_left_iff_imp]
        exact fun h => h.1.le
      rw [hset, Real.volume_Ioc, sub_zero]
    rw [hvalue]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.ne
  have hcount : ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ k : ℕ,
      N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) = k := by
    rw [ae_all_iff]
    intro T
    exact N.integer_valued (measurableSet_Ioc.prod hB) (hwindow T)
  have hdirac := Kyprianou.Ch02.prmFiniteWindowDiracLawV1 P ν N B hB hfinite
  filter_upwards [hcount, hdirac] with ω hωcount hωdirac t
  obtain ⟨T, hT⟩ := exists_nat_gt (t : ℝ)
  let R : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B
  obtain ⟨k, hk⟩ := hωcount T
  obtain ⟨s, hs⟩ := hωdirac T
  have htop : ((N.N ω).restrict R) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hk]
    exact ENNReal.natCast_ne_top k
  have hfull : Integrable (fun z : ℝ × ℝ => z.2) ((N.N ω).restrict R) := by
    rw [hs, integrable_finset_sum_measure]
    intro p hp
    by_cases hzero : ((N.N ω).restrict R) {p} = 0
    · rw [Measure.restrict_apply (measurableSet_singleton p)] at hzero
      dsimp only [R] at hzero
      simpa [hzero]
    · have hcoef : ((N.N ω).restrict R) {p} ≠ ⊤ :=
        ne_top_of_le_ne_top htop (measure_mono (Set.subset_univ _))
      exact (integrable_smul_measure hzero hcoef).2 (integrable_dirac (by simp))
  have hfullOn : IntegrableOn (fun z : ℝ × ℝ => z.2) R (N.N ω) := hfull
  refine hfullOn.mono_set ?_
  intro z hz
  exact ⟨⟨hz.1.1, hz.1.2.trans (le_of_lt hT)⟩, hz.2⟩
