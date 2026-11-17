-- Prove2me | solution 1 for Kyprianou.poissonRandomMeasureGenericCountableAtomsMeasurableSingletons
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:26:48.272566+00:00
-- url     : https://prove2.me/submissions/77ab3657-32e7-45e9-8616-c0bd642d331b

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem prm_atom_aux
    {Ω E : Type} [MeasurableSpace E] [MeasurableSingletonClass E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E) (ω : Ω) (z : E)
    (hz : ProbabilityTheory.poissonRandomMeasure K Y ω {z} ≠ 0) :
    ∃ k n, n < K k ω ∧ Y k n ω = z := by
  by_contra hcon
  push Not at hcon
  apply hz
  rw [ProbabilityTheory.poissonRandomMeasure, Measure.sum_apply _ (measurableSet_singleton z)]
  refine ENNReal.tsum_eq_zero.2 (fun k => ?_)
  rw [Measure.sum_apply _ (measurableSet_singleton z)]
  refine ENNReal.tsum_eq_zero.2 (fun n => ?_)
  split_ifs with h
  · rw [Measure.dirac_apply' _ (measurableSet_singleton z)]
    exact Set.indicator_of_notMem (fun hmem => hcon k n h (Set.mem_singleton_iff.1 hmem)) _
  · rfl

theorem prm_countable_aux
    {Ω E : Type} [MeasurableSpace E] [MeasurableSingletonClass E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E) (ω : Ω) :
    Set.Countable {z : E | ProbabilityTheory.poissonRandomMeasure K Y ω {z} ≠ 0} := by
  refine (Set.countable_range (fun p : ℕ × ℕ => Y p.1 p.2 ω)).mono ?_
  intro z hz
  obtain ⟨k, n, -, h⟩ := prm_atom_aux K Y ω z hz
  exact ⟨(k, n), h⟩

theorem prm_finite_aux
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hfamily : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    (m Set.univ < ⊤ →
      ∀ᵐ ω ∂P,
        Set.Finite
          {z : E | ProbabilityTheory.poissonRandomMeasure K Y ω {z} ≠ 0}) := by
  intro hfin
  have hsum : ∑' k, m (prmPiece m k) = m Set.univ := by
    rw [← measure_iUnion pairwise_disjoint_prmPiece (fun k => measurableSet_prmPiece),
      iUnion_prmPiece]
  have hle : ∀ k, P {ω | K k ω ∈ ({0} : Set ℕ)ᶜ} ≤ m (prmPiece m k) := by
    intro k
    have hlaw := hfamily.law_count k
    have hmeas := hfamily.measurable_count k
    have h1 : P {ω | K k ω ∈ ({0} : Set ℕ)ᶜ}
        = poissonMeasure (m (prmPiece m k)).toNNReal ({0} : Set ℕ)ᶜ := by
      rw [← hlaw.map_eq, Measure.map_apply hmeas (measurableSet_singleton 0).compl]
      rfl
    rw [h1, measure_compl (measurableSet_singleton 0) (measure_ne_top _ _), measure_univ,
      poissonMeasure_singleton]
    set r : ℝ≥0 := (m (prmPiece m k)).toNNReal with hr
    have hrm : ((r : ℝ≥0) : ℝ≥0∞) = m (prmPiece m k) :=
      ENNReal.coe_toNNReal (measure_prmPiece_lt_top).ne
    rw [← hrm, tsub_le_iff_right]
    have hpos : (0 : ℝ) ≤ Real.exp (-(r : ℝ)) * (r : ℝ) ^ 0 / (Nat.factorial 0) := by
      positivity
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (by positivity) hpos]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have := Real.add_one_le_exp (-(r : ℝ))
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
    linarith
  have hts : ∑' k, P {ω | K k ω ∈ ({0} : Set ℕ)ᶜ} ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [hsum]; exact hfin.ne
  filter_upwards [ae_eventually_notMem hts] with ω hω
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hω
  have hfinset : Set.Finite (⋃ k ∈ Finset.range N,
      (fun n => Y k n ω) '' Set.Iio (K k ω)) :=
    (Finset.range N).finite_toSet.biUnion (fun k _ => (Set.finite_Iio _).image _)
  refine hfinset.subset ?_
  intro z hz
  obtain ⟨k, n, hn, h⟩ := prm_atom_aux K Y ω z hz
  have hk : k < N := by
    by_contra hkN
    have := hN k (not_lt.1 hkN)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] at this
    omega
  simp only [Set.mem_iUnion]
  exact ⟨k, Finset.mem_range.2 hk, n, hn, h⟩

theorem poissonRandomMeasureGenericCountableAtomsMeasurableSingletons
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hfamily : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    (∀ᵐ ω ∂P,
      Set.Countable
        {z : E | ProbabilityTheory.poissonRandomMeasure K Y ω {z} ≠ 0}) :=
  Filter.Eventually.of_forall (fun ω => prm_countable_aux K Y ω)

end Kyprianou

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hfamily : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    (∀ᵐ ω ∂P,
      Set.Countable
        {z : E | ProbabilityTheory.poissonRandomMeasure K Y ω {z} ≠ 0}) :=
  Kyprianou.poissonRandomMeasureGenericCountableAtomsMeasurableSingletons P m K Y hfamily
