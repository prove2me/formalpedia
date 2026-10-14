-- Prove2me | solution 1 for NagaevLD.LowerBound.clear_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T21:42:18.02683+00:00
-- url     : https://prove2.me/submissions/2f646c93-df16-4d42-aff2-0a823771ea1e

import Mathlib
import Definitions.Def_NagaevLD_LowerBound_Setting

open MeasureTheory ProbabilityTheory


namespace NagaevLD.LowerBound

theorem eq_1_57_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (x : ℝ) :
    ∑ j, Pj P X x j ≤ P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω} := by
  classical
  let A : Fin n → Set Ω := fun j =>
    {ω | x ≤ NagaevLD.FukNagaev.S n X ω ∧ x ≤ X j ω ∧ ∀ i, i ≠ j → X i ω < x}
  have hSm : Measurable (NagaevLD.FukNagaev.S n X) := by
    unfold NagaevLD.FukNagaev.S
    exact Finset.measurable_fun_sum _ (fun i _ => hXm i)
  have hAm : ∀ j, MeasurableSet (A j) := by
    intro j
    have h1 : MeasurableSet {ω | x ≤ NagaevLD.FukNagaev.S n X ω} :=
      measurableSet_le measurable_const hSm
    have h2 : MeasurableSet {ω | x ≤ X j ω} := measurableSet_le measurable_const (hXm j)
    have h3 : MeasurableSet {ω | ∀ i, i ≠ j → X i ω < x} := by
      have : {ω | ∀ i, i ≠ j → X i ω < x} = ⋂ i, ⋂ (_ : i ≠ j), {ω | X i ω < x} := by
        ext ω; simp
      rw [this]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
        measurableSet_lt (hXm i) measurable_const
    exact h1.inter (h2.inter h3)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) A := by
    intro j _ k _ hjk
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨_, _, hj⟩ ⟨_, hk, _⟩
    exact absurd (hj k (Ne.symm hjk)) (not_lt.mpr hk)
  have h := measureReal_biUnion_finset (μ := P) hdisj (fun b _ => hAm b)
  have hsub : (⋃ b ∈ (Finset.univ : Finset (Fin n)), A b) ⊆
      {ω | x ≤ NagaevLD.FukNagaev.S n X ω} := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω
    obtain ⟨b, _, hb⟩ := hω
    exact hb.1
  calc ∑ j, Pj P X x j = ∑ j, P.real (A j) := rfl
    _ = P.real (⋃ b ∈ (Finset.univ : Finset (Fin n)), A b) := h.symm
    _ ≤ _ := measureReal_mono hsub

theorem clear_step_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (x : ℝ) (j : Fin n) :
    P.real {ω | -x ≤ Sj n X j ω} - P.real {ω | ∃ i, i ≠ j ∧ x ≤ X i ω} ≤
      P.real {ω | -x ≤ Sj n X j ω ∧ ∀ i, i ≠ j → X i ω < x} := by
  have hsub : {ω | -x ≤ Sj n X j ω} ⊆
      {ω | -x ≤ Sj n X j ω ∧ ∀ i, i ≠ j → X i ω < x} ∪ {ω | ∃ i, i ≠ j ∧ x ≤ X i ω} := by
    intro ω hω
    by_cases h : ∀ i, i ≠ j → X i ω < x
    · exact Or.inl ⟨hω, h⟩
    · push_neg at h
      exact Or.inr h
  have := (measureReal_mono hsub (μ := P)).trans (measureReal_union_le _ _)
  linarith

/-- Chebyshev-type tail bound for a single centred summand. -/
theorem single_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : MemLp Y 2 P) (hmean : ∫ ω, Y ω ∂P = 0) (x : ℝ) (hx : 0 < x) :
    P.real {ω | x ≤ |Y ω|} ≤ variance Y P / x ^ 2 := by
  have h := meas_ge_le_variance_div_sq hY hx
  have hset : {ω | x ≤ |Y ω - ∫ ω, Y ω ∂P|} = {ω | x ≤ |Y ω|} := by
    ext ω; simp [hmean]
  rw [hset] at h
  have hnn : 0 ≤ variance Y P / x ^ 2 := div_nonneg (variance_nonneg _ _) (by positivity)
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hnn h

theorem chebyshev_max_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (x : ℝ) (hx : 0 < x) (j : Fin n) :
    P.real {ω | ∃ i, i ≠ j ∧ x ≤ X i ω} ≤ NagaevLD.FukNagaev.Bn2 P X / x ^ 2 := by
  classical
  have hsub : {ω | ∃ i, i ≠ j ∧ x ≤ X i ω} ⊆
      ⋃ i ∈ (Finset.univ.erase j : Finset (Fin n)), {ω | x ≤ |X i ω|} := by
    intro ω ⟨i, hij, hi⟩
    simp only [Set.mem_iUnion, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨i, hij, hi.trans (le_abs_self _)⟩
  calc P.real {ω | ∃ i, i ≠ j ∧ x ≤ X i ω}
      ≤ P.real (⋃ i ∈ (Finset.univ.erase j : Finset (Fin n)), {ω | x ≤ |X i ω|}) :=
        measureReal_mono hsub (h₂ := measure_ne_top _ _)
    _ ≤ ∑ i ∈ Finset.univ.erase j, P.real {ω | x ≤ |X i ω|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ Finset.univ.erase j, variance (X i) P / x ^ 2 :=
        Finset.sum_le_sum fun i _ => single_tail P (X i) (hL2 i) (hmean i) x hx
    _ ≤ ∑ i, variance (X i) P / x ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun i _ _ => div_nonneg (variance_nonneg _ _) (by positivity))
    _ = NagaevLD.FukNagaev.Bn2 P X / x ^ 2 := by
        rw [NagaevLD.FukNagaev.Bn2, Finset.sum_div]

theorem chebyshev_Sj_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun (fun i => X i) P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (x : ℝ) (hx : 0 < x) (j : Fin n) :
    1 - NagaevLD.FukNagaev.Bn2 P X / x ^ 2 ≤ P.real {ω | -x ≤ Sj n X j ω} := by
  classical
  have hfun : Sj n X j = ∑ i ∈ Finset.univ.erase j, X i := by
    funext ω; simp [Sj, Finset.sum_apply]
  have hL2S : MemLp (Sj n X j) 2 P := by
    rw [hfun]; exact memLp_finsetSum' _ (fun i _ => hL2 i)
  have hmeanS : ∫ ω, Sj n X j ω ∂P = 0 := by
    simp only [Sj]
    rw [integral_finsetSum _ (fun i _ => (hL2 i).integrable one_le_two)]
    exact Finset.sum_eq_zero fun i _ => hmean i
  have hvar : variance (Sj n X j) P ≤ NagaevLD.FukNagaev.Bn2 P X := by
    rw [hfun, IndepFun.variance_sum (fun i _ => hL2 i)]
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun i _ _ => variance_nonneg _ _)
    · intro i _ k _ hik
      exact hindep.indepFun hik
  have htail := single_tail P (Sj n X j) hL2S hmeanS x hx
  have hsub : {ω | -x ≤ Sj n X j ω}ᶜ ⊆ {ω | x ≤ |Sj n X j ω|} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω ⊢
    rw [abs_of_neg (by linarith)]; linarith
  have hm : MeasurableSet {ω | -x ≤ Sj n X j ω} := by
    refine measurableSet_le measurable_const ?_
    unfold Sj
    exact Finset.measurable_sum _ (fun i _ => hXm i)
  have hc := measureReal_compl (μ := P) hm
  have h2 := measureReal_mono hsub (μ := P)
  simp only [probReal_univ] at hc
  have h3 : variance (Sj n X j) P / x ^ 2 ≤ NagaevLD.FukNagaev.Bn2 P X / x ^ 2 :=
    div_le_div_of_nonneg_right hvar (by positivity)
  linarith

end NagaevLD.LowerBound

open NagaevLD.LowerBound


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (x : ℝ) (j : Fin n) :
    P.real {ω | -x ≤ Sj n X j ω} - P.real {ω | ∃ i, i ≠ j ∧ x ≤ X i ω} ≤
      P.real {ω | -x ≤ Sj n X j ω ∧ ∀ i, i ≠ j → X i ω < x} := by
  exact clear_step_core P n X x j
