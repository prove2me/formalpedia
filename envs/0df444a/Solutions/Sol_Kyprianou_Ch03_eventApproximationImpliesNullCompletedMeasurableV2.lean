-- Prove2me | solution 1 for Kyprianou.Ch03.eventApproximationImpliesNullCompletedMeasurableV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:14:30.859112+00:00
-- url     : https://prove2.me/submissions/0762e76c-883f-4b9f-9841-4b1a8f091df9

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m : MeasurableSpace Omega) (A : Set Omega)
    (hApprox : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ B : Set Omega, MeasurableSet[m] B ∧
        P ((A \ B) ∪ (B \ A)) < ε) :
    MeasurableSet[m ⊔ MeasurableSpace.generateFrom
      {N : Set Omega | ∃ M : Set Omega,
        MeasurableSet[mΩ] M ∧ P M = 0 ∧ N ⊆ M}] A := by
  classical
  letI : MeasurableSpace Omega := mΩ
  have hhalf : 0 < (1 / 2 : ℝ≥0∞) := by norm_num
  choose B hB hErr using fun n : ℕ =>
    hApprox ((1 / 2 : ℝ≥0∞) ^ n) (ENNReal.pow_pos hhalf n)
  let D : ℕ → Set Omega := fun n => (A \ B n) ∪ (B n \ A)
  have hsum : (∑' n, P (D n)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum fun n => (hErr n).le)
    rw [ENNReal.tsum_geometric]
    norm_num
  have hzero : P (limsup D atTop) = 0 :=
    measure_limsup_atTop_eq_zero (μ := @Measure.toOuterMeasure Omega mΩ P) hsum
  obtain ⟨N, hDN, hNm, hN0⟩ :=
    @exists_measurable_superset_of_null Omega mΩ P (limsup D atTop) hzero
  let L := liminf B atTop
  have hLm : MeasurableSet[m] L :=
    @MeasurableSet.measurableSet_liminf Omega m B hB
  let mc := m ⊔ MeasurableSpace.generateFrom
    {N : Set Omega | ∃ M : Set Omega,
      MeasurableSet[mΩ] M ∧ P M = 0 ∧ N ⊆ M}
  have hL : MeasurableSet[mc] L :=
    (le_sup_left : m ≤ mc) L hLm
  have hnull (S : Set Omega) (hS : S ⊆ N) : MeasurableSet[mc] S := by
    apply (le_sup_right : _ ≤ mc) S
    exact MeasurableSpace.measurableSet_generateFrom ⟨N, hNm, hN0, hS⟩
  have heq (x : Omega) (hx : x ∉ N) : x ∈ A ↔ x ∈ L := by
    have hn : x ∉ limsup D atTop := fun hd => hx (hDN hd)
    rw [mem_limsup_iff_frequently_mem] at hn
    have hev : ∀ᶠ n in atTop, x ∉ D n := by
      exact Filter.not_frequently.mp hn
    change x ∈ A ↔ x ∈ liminf B atTop
    rw [mem_liminf_iff_eventually_mem]
    constructor
    · intro ha
      filter_upwards [hev] with n hd
      simp [D] at hd
      tauto
    · intro hb
      have hh : ∀ᶠ n : ℕ in atTop, x ∈ A := by
        filter_upwards [hev, hb] with n hd hbn
        simp [D] at hd
        tauto
      exact eventually_const.mp hh
  have hA : A = (L \ N) ∪ (A ∩ N) := by
    ext x
    by_cases hx : x ∈ N
    · simp [hx]
    · simp [hx, ← heq x hx]
  rw [hA]
  exact (hL.diff (hnull N (fun _ h => h))).union (hnull (A ∩ N) Set.inter_subset_right)
