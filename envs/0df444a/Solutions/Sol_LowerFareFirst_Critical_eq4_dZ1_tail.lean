-- Prove2me | solution 1 for LowerFareFirst.Critical.eq4_dZ1_tail
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:18:05.337207+00:00
-- url     : https://prove2.me/submissions/8886487e-022e-49ef-a840-9776e63c4ba7

import Mathlib
import Definitions.Def_LowerFareFirst_Critical_Model

set_option autoImplicit false

open MeasureTheory LowerFareFirst.Critical

lemma lfc_fare_pos {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (c : ℕ) (hM : IsSeatModel μ D r c) :
    ∀ m, 1 ≤ m → m ≤ c → 0 < r m := by
  have key : ∀ d m : ℕ, m + d = c → 1 ≤ m → 0 < r m := by
    intro d
    induction d with
    | zero => intro m hm _; simp at hm; subst hm; exact hM.fare_pos
    | succ d ih =>
      intro m hm h1
      have := ih (m + 1) (by omega) (by omega)
      have h2 := hM.fare_strictAnti m h1 (by omega)
      linarith
  intro m h1 h2
  exact key (c - m) m (by omega) h1

lemma lfc_Z1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (c : ℕ) (hM : IsSeatModel μ D r c) (n : ℕ) :
    Z μ D r 1 n = r 1 * ((n : ℝ) * probGe μ D 1 n + ∑ j ∈ Finset.range n, (j : ℝ) * probEq μ D 1 j) := by
  haveI := hM.isProb
  have hr1 : 0 < r 1 := lfc_fare_pos μ D r c hM 1 le_rfl (by have := hM.two_le; omega)
  have hmeas : ∀ j, MeasurableSet {ω | D 1 ω = j} := fun j =>
    (hM.meas 1) (measurableSet_singleton j)
  have hmeas2 : MeasurableSet {ω | n ≤ D 1 ω} := (hM.meas 1) (measurableSet_Ici)
  have hZ0 : ∀ k, Z μ D r 0 k = 0 := fun k => by simp [Z]
  have hsup : ∀ d : ℕ, (Finset.range (min d n + 1)).sup' Finset.nonempty_range_add_one
        (fun x => r 1 * (x : ℝ) + Z μ D r 0 (n - x)) = r 1 * ((min d n : ℕ) : ℝ) := by
    intro d
    simp only [hZ0, add_zero]
    apply le_antisymm
    · refine Finset.sup'_le _ _ (fun x hx => ?_)
      have hx' : x ≤ min d n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hx)
      have h1 : (x : ℝ) ≤ ((min d n : ℕ) : ℝ) := by exact_mod_cast hx'
      exact mul_le_mul_of_nonneg_left h1 hr1.le
    · exact Finset.le_sup' (fun x : ℕ => r 1 * (x : ℝ)) (Finset.mem_range.2 (Nat.lt_succ_self (min d n)))
  have hZ : Z μ D r 1 n = ∫ ω, r 1 * ((min (D 1 ω) n : ℕ) : ℝ) ∂μ := by
    show (∫ ω, (Finset.range (min (D 1 ω) n + 1)).sup' Finset.nonempty_range_add_one
        (fun x => r 1 * (x : ℝ) + Z μ D r 0 (n - x)) ∂μ) = _
    simp_rw [hsup]
  have hpt : ∀ ω, ((min (D 1 ω) n : ℕ) : ℝ) =
      ∑ j ∈ Finset.range n, (j : ℝ) * ({ω | D 1 ω = j}.indicator (fun _ => (1 : ℝ)) ω) +
        (n : ℝ) * ({ω | n ≤ D 1 ω}.indicator (fun _ => (1 : ℝ)) ω) := by
    intro ω
    by_cases h : D 1 ω < n
    · have h1 : min (D 1 ω) n = D 1 ω := min_eq_left h.le
      rw [h1, Finset.sum_eq_single (D 1 ω)]
      · simp [Set.indicator, not_le.2 h]
      · intro j _ hj
        simp [Set.indicator, Ne.symm hj]
      · intro hn; exact absurd (Finset.mem_range.2 h) hn
    · push_neg at h
      have h1 : min (D 1 ω) n = n := min_eq_right h
      rw [h1, Finset.sum_eq_zero]
      · simp [Set.indicator, h]
      · intro j hj
        have : D 1 ω ≠ j := by have := Finset.mem_range.1 hj; omega
        simp [Set.indicator, this]
  have hi1 : ∀ j : ℕ, Integrable (fun ω => (j : ℝ) * ({ω | D 1 ω = j}.indicator (fun _ => (1 : ℝ)) ω)) μ := by
    intro j
    exact ((integrable_const (1 : ℝ)).indicator (hmeas j)).const_mul _
  have hi2 : Integrable (fun ω => (n : ℝ) * ({ω | n ≤ D 1 ω}.indicator (fun _ => (1 : ℝ)) ω)) μ :=
    ((integrable_const (1 : ℝ)).indicator hmeas2).const_mul _
  have hsum : Integrable (fun ω => ∑ j ∈ Finset.range n,
      (j : ℝ) * ({ω | D 1 ω = j}.indicator (fun _ => (1 : ℝ)) ω)) μ :=
    integrable_finset_sum _ (fun j _ => hi1 j)
  have hfs : ∫ ω, ∑ j ∈ Finset.range n,
      (j : ℝ) * ({ω | D 1 ω = j}.indicator (fun _ => (1 : ℝ)) ω) ∂μ =
      ∑ j ∈ Finset.range n, ∫ ω, (j : ℝ) * ({ω | D 1 ω = j}.indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
    integral_finset_sum _ (fun j _ => hi1 j)
  have e1 : ∀ j : ℕ, ∫ ω, (j : ℝ) * ({ω | D 1 ω = j}.indicator (fun _ => (1 : ℝ)) ω) ∂μ =
      (j : ℝ) * probEq μ D 1 j := by
    intro j
    rw [integral_const_mul, integral_indicator_const _ (hmeas j)]
    simp [probEq]
  have e2 : ∫ ω, (n : ℝ) * ({ω | n ≤ D 1 ω}.indicator (fun _ => (1 : ℝ)) ω) ∂μ =
      (n : ℝ) * probGe μ D 1 n := by
    rw [integral_const_mul, integral_indicator_const _ hmeas2]
    simp [probGe]
  have hint : ∫ ω, ((min (D 1 ω) n : ℕ) : ℝ) ∂μ =
      ∑ j ∈ Finset.range n, (j : ℝ) * probEq μ D 1 j + (n : ℝ) * probGe μ D 1 n := by
    have : (fun ω => ((min (D 1 ω) n : ℕ) : ℝ)) = fun ω => ∑ j ∈ Finset.range n,
        (j : ℝ) * ({ω | D 1 ω = j}.indicator (fun _ => (1 : ℝ)) ω) +
        (n : ℝ) * ({ω | n ≤ D 1 ω}.indicator (fun _ => (1 : ℝ)) ω) := funext hpt
    rw [this, integral_add hsum hi2, hfs, e2]
    simp_rw [e1]
  rw [hZ, integral_const_mul, hint]
  ring

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (c : ℕ)
    (hM : IsSeatModel μ D r c) :
    (∀ n : ℕ, 1 ≤ n → dZ μ D r 1 n = r 1 * probGe μ D 1 n) ∧
      (∀ n : ℕ, 1 ≤ n → dZ μ D r 1 (n + 1) ≤ dZ μ D r 1 n) := by
  haveI := hM.isProb
  have hr1 : 0 < r 1 := lfc_fare_pos μ D r c hM 1 le_rfl (by have := hM.two_le; omega)
  have hmeas : ∀ j, MeasurableSet {ω | D 1 ω = j} := fun j =>
    (hM.meas 1) (measurableSet_singleton j)
  have hmeas2 : ∀ n, MeasurableSet {ω | n ≤ D 1 ω} := fun n => (hM.meas 1) (measurableSet_Ici)
  have hge : ∀ n : ℕ, probGe μ D 1 n = probEq μ D 1 n + probGe μ D 1 (n + 1) := by
    intro n
    unfold probGe probEq
    have : {ω | n ≤ D 1 ω} = {ω | D 1 ω = n} ∪ {ω | n + 1 ≤ D 1 ω} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_union]; omega
    rw [this, measureReal_union _ (hmeas2 (n + 1))]
    rw [Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    omega
  have h1 : ∀ n : ℕ, 1 ≤ n → dZ μ D r 1 n = r 1 * probGe μ D 1 n := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    unfold dZ
    simp only [Nat.add_sub_cancel]
    rw [lfc_Z1 μ D r c hM (k + 1), lfc_Z1 μ D r c hM k, Finset.sum_range_succ, hge k]
    push_cast
    ring
  refine ⟨h1, fun n hn => ?_⟩
  rw [h1 n hn, h1 (n + 1) (by omega)]
  refine mul_le_mul_of_nonneg_left ?_ hr1.le
  unfold probGe
  exact measureReal_mono (fun ω hω => by simp only [Set.mem_setOf_eq] at hω ⊢; omega)
