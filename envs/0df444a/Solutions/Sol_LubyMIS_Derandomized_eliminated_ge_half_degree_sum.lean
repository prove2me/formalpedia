-- Prove2me | solution 1 for LubyMIS.Derandomized.eliminated_ge_half_degree_sum
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:13:55.849435+00:00
-- url     : https://prove2.me/submissions/49e635a0-41bc-4bdc-8204-cfc54cd2e20c

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic

open MeasureTheory ProbabilityTheory

namespace LubyMIS.Derandomized

theorem aux_lmis_pointwise {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (T : Finset V) :
    (∑ i ∈ T ∪ nbhd H T, (H.degree i : ℝ)) ≤ 2 * (eliminated H T : ℝ) := by
  classical
  set Y := T ∪ nbhd H T with hY
  set E' := H.edgeFinset.filter (fun e => ∃ v ∈ e, v ∈ Y) with hE'
  have hel : eliminated H T = E'.card := by
    unfold eliminated
    rw [hE']
  have key : ∑ i ∈ Y, H.degree i ≤ 2 * E'.card := by
    have h1 : ∀ i ∈ Y, H.degree i = (E'.bipartiteAbove (fun i e => i ∈ e) i).card := by
      intro i hi
      rw [← SimpleGraph.card_incidenceFinset_eq_degree]
      congr 1
      ext e
      simp only [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, Set.mem_ofPred_eq,
        Finset.mem_bipartiteAbove, E', Finset.mem_filter, SimpleGraph.mem_edgeFinset]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, i, h2, hi⟩, h2⟩
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨h1, h2⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    calc ∑ e ∈ E', (Y.bipartiteBelow (fun i e => i ∈ e) e).card ≤ ∑ e ∈ E', 2 := by
          apply Finset.sum_le_sum
          intro e _
          induction e using Sym2.ind with
          | h a b =>
            calc _ ≤ ({a, b} : Finset V).card := by
                  apply Finset.card_le_card
                  intro v hv
                  simp only [Finset.mem_bipartiteBelow, Sym2.mem_iff] at hv
                  simp only [Finset.mem_insert, Finset.mem_singleton]
                  exact hv.2
              _ ≤ 2 := Finset.card_le_two
      _ = 2 * E'.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have : ((∑ i ∈ Y, H.degree i : ℕ) : ℝ) ≤ ((2 * E'.card : ℕ) : ℝ) := by exact_mod_cast key
  push_cast at this
  rw [hel]
  exact this

theorem aux_lmis_meas {V : Type*} [Fintype V] {Ω : Type*} [MeasurableSpace Ω]
    (S : Ω → Finset V) (hS : ∀ i, MeasurableSet {ω | i ∈ S ω}) (A : Set (Finset V)) :
    MeasurableSet (S ⁻¹' A) := by
  have h1 : ∀ T : Finset V, MeasurableSet (S ⁻¹' {T}) := by
    intro T
    have : S ⁻¹' {T} = ⋂ i, {ω | i ∈ S ω ↔ i ∈ T} := by
      ext ω; simp [Finset.ext_iff]
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    by_cases hi : i ∈ T
    · convert hS i using 1
      ext ω; simp [hi]
    · convert (hS i).compl using 1
      ext ω; simp [hi]
  have : S ⁻¹' A = ⋃ T ∈ A, S ⁻¹' {T} := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable A) fun T _ => h1 T

theorem aux_lmis_integrable {V : Type*} [Fintype V] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Finset V) (hS : ∀ i, MeasurableSet {ω | i ∈ S ω}) (g : Finset V → ℝ) :
    Integrable (fun ω => g (S ω)) μ := by
  have hm : Measurable (fun ω => g (S ω)) := fun s _ => aux_lmis_meas S hS (g ⁻¹' s)
  refine Integrable.of_bound hm.aestronglyMeasurable (∑ T, |g T|) (Filter.Eventually.of_forall ?_)
  intro ω
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun T => |g T|) (fun T _ => abs_nonneg _) (Finset.mem_univ _)

end LubyMIS.Derandomized

open LubyMIS.Derandomized

open MeasureTheory ProbabilityTheory

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Ω → Finset V) (hS : ∀ i, MeasurableSet {ω | i ∈ S ω}) :
    (∫ ω, (eliminated H (S ω) : ℝ) ∂μ) ≥
        1 / 2 * ∑ i, (H.degree i : ℝ) * μ.real {ω | i ∈ S ω ∪ nbhd H (S ω)} ∧
      1 / 2 * ∑ i, (H.degree i : ℝ) * μ.real {ω | i ∈ S ω ∪ nbhd H (S ω)} ≥
        1 / 2 * ∑ i, (H.degree i : ℝ) * μ.real {ω | i ∈ nbhd H (S ω)} := by
  constructor
  · have hmeas : ∀ i : V, MeasurableSet {ω | i ∈ S ω ∪ nbhd H (S ω)} := fun i =>
      aux_lmis_meas S hS {T | i ∈ T ∪ nbhd H T}
    have hint : ∀ i : V, Integrable
        (fun ω => (H.degree i : ℝ) * ({ω | i ∈ S ω ∪ nbhd H (S ω)}.indicator 1 ω)) μ := by
      intro i
      exact ((integrable_const (1 : ℝ)).indicator (hmeas i)).const_mul _
    have hrhs : 1 / 2 * ∑ i, (H.degree i : ℝ) * μ.real {ω | i ∈ S ω ∪ nbhd H (S ω)} =
        ∫ ω, 1 / 2 * ∑ i, (H.degree i : ℝ) *
          ({ω | i ∈ S ω ∪ nbhd H (S ω)}.indicator 1 ω) ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => hint i)]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_indicator_one (hmeas i)]
    rw [hrhs, ge_iff_le]
    apply integral_mono
    · exact (integrable_finsetSum _ (fun i _ => hint i)).const_mul _
    · exact aux_lmis_integrable μ S hS (fun T => (eliminated H T : ℝ))
    · intro ω
      have hp := aux_lmis_pointwise H (S ω)
      have : ∑ i, (H.degree i : ℝ) * ({ω | i ∈ S ω ∪ nbhd H (S ω)}.indicator 1 ω) =
          ∑ i ∈ S ω ∪ nbhd H (S ω), (H.degree i : ℝ) := by
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, mul_ite, mul_one,
          mul_zero]
        rw [← Finset.sum_filter]
        congr 1
        ext i; simp
      simp only
      rw [this]
      linarith
  · rw [ge_iff_le]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    simp only [Set.mem_ofPred_eq, Finset.mem_union] at hω ⊢
    exact Or.inr hω
