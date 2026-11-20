-- Prove2me | solution 1 for LevyStochCalc.Poisson.ae_isIntegerValued_restrict
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:58:46.9468+00:00
-- url     : https://prove2.me/submissions/3775f933-a219-44c2-a515-18a6190b443a

import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section CountablyGenerated

variable [MeasurableSpace.CountablyGenerated E]

theorem AuxAiv.tsum_nat {ι : Type*} (k : ι → ℕ) (h : ∑' i, (k i : ℝ≥0∞) ≠ ⊤) :
    ∃ n : ℕ, ∑' i, (k i : ℝ≥0∞) = n := by
  have hfin : {i | k i ≠ 0}.Finite := by
    refine (ENNReal.finite_const_le_of_tsum_ne_top h one_ne_zero).subset fun i hi => ?_
    simp only [Set.mem_setOf_eq] at hi ⊢
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hi
  refine ⟨∑ i ∈ hfin.toFinset, k i, ?_⟩
  rw [tsum_eq_sum (s := hfin.toFinset)]
  · push_cast; rfl
  · intro i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hi
    simp [hi]

theorem _root_.solution (N : PoissonRandomMeasure P ν) {R : Set (ℝ × E)}
    (hRm : MeasurableSet R) (hRfin : referenceIntensity ν R ≠ ⊤) :
    ∀ᵐ ω ∂P, Probability.IsIntegerValued ((N.N ω).restrict R) := by
  have hcount : (markPiSystem E).Countable := Probability.countable_finInters _
  have hmeasπ : ∀ B ∈ markPiSystem E, MeasurableSet B :=
    Probability.measurableSet_of_mem_finInters
      (MeasurableSpace.measurableSet_natGeneratingSequence)
  have hB : ∀ B ∈ markPiSystem E, ∀ᵐ ω ∂P, ∃ n : ℕ, N.N ω (B ∩ R) = n := by
    intro B hB
    refine N.integer_valued ((hmeasπ B hB).inter hRm) ?_
    exact ne_top_of_le_ne_top hRfin (measure_mono Set.inter_subset_right)
  have hall : ∀ᵐ ω ∂P, ∀ B ∈ markPiSystem E, ∃ n : ℕ, N.N ω (B ∩ R) = n :=
    (ae_ball_iff hcount).2 hB
  filter_upwards [hall, N.integer_valued hRm hRfin] with ω hω hR
  obtain ⟨nR, hnR⟩ := hR
  intro B hBm
  rw [Measure.restrict_apply hBm]
  refine MeasurableSpace.induction_on_inter (C := fun B _ => ∃ n : ℕ, N.N ω (B ∩ R) = n)
    generateFrom_markPiSystem.symm isPiSystem_markPiSystem ?_ ?_ ?_ ?_ B hBm
  · exact ⟨0, by simp⟩
  · intro t ht; exact hω t ht
  · rintro t htm ⟨k, hk⟩
    have hsub : t ∩ R ⊆ R := Set.inter_subset_right
    have e : tᶜ ∩ R = R \ (t ∩ R) := by ext x; simp; tauto
    have hle : k ≤ nR := by
      have := measure_mono (μ := N.N ω) hsub
      rw [hk, hnR] at this
      exact_mod_cast this
    refine ⟨nR - k, ?_⟩
    rw [e, measure_sdiff hsub (htm.inter hRm).nullMeasurableSet (by rw [hk]; exact ENNReal.natCast_ne_top k),
      hnR, hk, ENNReal.natCast_sub]
  · intro f hdisj hfm hf
    choose k hk using hf
    have e : (⋃ i, f i) ∩ R = ⋃ i, (f i ∩ R) := Set.iUnion_inter R f
    have hd : Pairwise (Function.onFun Disjoint fun i => f i ∩ R) := fun i j hij =>
      (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
    rw [e, measure_iUnion hd (fun i => (hfm i).inter hRm)]
    simp_rw [hk]
    refine AuxAiv.tsum_nat k ?_
    have : ∑' i, (k i : ℝ≥0∞) ≤ N.N ω R :=
      calc ∑' i, (k i : ℝ≥0∞) = ∑' i, N.N ω (f i ∩ R) := by simp_rw [hk]
        _ = N.N ω (⋃ i, f i ∩ R) := (measure_iUnion hd (fun i => (hfm i).inter hRm)).symm
        _ ≤ N.N ω R := measure_mono (Set.iUnion_subset fun i => Set.inter_subset_right)
    exact ne_top_of_le_ne_top (by rw [hnR]; exact ENNReal.natCast_ne_top nR) this

end CountablyGenerated

end LevyStochCalc.Poisson
