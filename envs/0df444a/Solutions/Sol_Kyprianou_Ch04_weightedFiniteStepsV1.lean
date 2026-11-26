-- Prove2me | solution 1 for Kyprianou.Ch04.weightedFiniteStepsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:51:30.840886+00:00
-- url     : https://prove2.me/submissions/0c12b8ee-0079-4d46-b344-c9bfc2a2b63b

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Common-event finite-step representation of arbitrary weighted marked integrals. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (g : ℝ × ℝ → Ω → ℝ)
    (hDirac : ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      (N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) =
        ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B)) {p} • Measure.dirac p) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ (s : Finset (ℝ × ℝ))
      (weight : ℝ × ℝ → ℝ), ∀ t : ℝ≥0, t ≤ (T : ℝ≥0) →
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), g z ω ∂(N.N ω)) =
        ∑ p ∈ s, if p.1 ≤ (t : ℝ) then weight p else 0  := by
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
  have hmass : ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ k : ℕ,
      N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) = k := by
    rw [ae_all_iff]
    intro T
    exact N.integer_valued (measurableSet_Ioc.prod hB) (hwindow T)
  filter_upwards [hDirac, hmass] with ω hω hωmass
  intro T
  obtain ⟨s, hs⟩ := hω T
  obtain ⟨k, hk⟩ := hωmass T
  let R : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B
  haveI : IsFiniteMeasure ((N.N ω).restrict R) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hk]
    exact ENNReal.natCast_lt_top k
  have hrepl (g : ℝ × ℝ → ℝ) :
      ∫ p in R, g p ∂(N.N ω) =
        ∑ p ∈ s, (((N.N ω).restrict R) {p}).toReal * g p := by
    conv_lhs => rw [hs]
    rw [integral_finsetSum_measure fun p _ =>
      (integrable_dirac (by simp)).smul_measure
        (measure_ne_top ((N.N ω).restrict R) _)]
    exact Finset.sum_congr rfl fun p _ => by
      rw [integral_smul_measure, integral_dirac, smul_eq_mul]
  let coeff : ℝ × ℝ → ℝ :=
    fun p => (((N.N ω).restrict R) {p}).toReal
  refine ⟨s, (fun p => coeff p * g p ω), ?_⟩
  intro t ht
  let S : Set (ℝ × ℝ) := {p | p.1 ≤ (t : ℝ)}
  have hS : MeasurableSet S := measurableSet_le measurable_fst measurable_const
  have htT : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
  have hset : R ∩ S = Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B := by
    ext p
    simp only [R, S, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨⟨hzero, hupper⟩, hmark⟩, htime⟩
      exact ⟨⟨hzero, htime⟩, hmark⟩
    · rintro ⟨⟨hzero, htime⟩, hmark⟩
      exact ⟨⟨⟨hzero, htime.trans htT⟩, hmark⟩, htime⟩
  have heq := hrepl (fun p => S.indicator (fun z => g z ω) p)
  change (∫ p in R, S.indicator (fun z => g z ω) p ∂(N.N ω)) =
    ∑ p ∈ s, coeff p * S.indicator (fun z => g z ω) p at heq
  rw [setIntegral_indicator hS, hset] at heq
  calc
    (∫ z in Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B, g z ω ∂(N.N ω)) =
        ∑ p ∈ s, coeff p * S.indicator (fun z => g z ω) p := heq
    _ = ∑ p ∈ s, if p.1 ≤ (t : ℝ) then coeff p * g p ω else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpt : p.1 ≤ (t : ℝ)
      · simp [S, Set.indicator, hpt]
      · simp [S, Set.indicator, hpt]
