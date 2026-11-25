-- Prove2me | solution 1 for GlobalTheory.Harm.casimir_value_strict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:47:42.83021+00:00
-- url     : https://prove2.me/submissions/794c03ad-8d8a-45de-bd45-9cec9e9c6c2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EqZeroOfPartialSumsNonneg
import Theorems.Thm_GlobalTheory_Harm_sum_filter_lt_eq_sum_range
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.Harm
open Finset
open Finset in
private theorem sum_range_sub_mul_eq_abel_summation (D e : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ range n, (D (i + 1) - D i) * e i =
      D n * e n + ∑ i ∈ range n, D (i + 1) * (e i - e (i + 1)) - D 0 * e 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, sum_range_succ, ih]; ring
end GlobalTheory.Harm
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.Harm
open Finset
open Finset
namespace GlobalTheory.Harm
namespace _root_.GlobalTheory.Harm
theorem _root_.solution {m : ℕ} (κ κ₀ : Fin m → ℤ) (h : Antitone κ)
    (h₀ : Antitone κ₀)
    (hle : ∀ i : ℕ, ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), κ k ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), κ₀ k)
    (hsum : ∑ k, κ k = ∑ k, κ₀ k)
    (hC : ∑ i, κ₀ i * (κ₀ i + m - 1 - 2 * (i : ℕ)) ≤ ∑ i, κ i * (κ i + m - 1 - 2 * (i : ℕ))) : κ = κ₀ := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℤ, d = fun j =>
      (if h : j < m then κ₀ ⟨j, h⟩ else 0) - (if h : j < m then κ ⟨j, h⟩ else 0) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℤ, e = fun j =>
      if h : j < m then κ₀ ⟨j, h⟩ + κ ⟨j, h⟩ + (m : ℤ) - 1 - 2 * (j : ℤ) else 0 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℤ, D = fun j => ∑ i ∈ range j, d i := ⟨_, rfl⟩
  have hDj : ∀ j, D j = ∑ k ∈ univ.filter (fun k : Fin m => (k : ℕ) < j), κ₀ k -
      ∑ k ∈ univ.filter (fun k : Fin m => (k : ℕ) < j), κ k := by
    intro j
    simp only [hD, hd, sum_sub_distrib, _root_.GlobalTheory.Harm.sum_filter_lt_eq_sum_range]
  have hD0 : ∀ j, 0 ≤ D j := fun j => by rw [hDj]; linarith [hle j]
  have hDm : D m = 0 := by rw [hDj]; simp [hsum]
  have hDzero : D 0 = 0 := by simp [hD]
  have hdD : ∀ j, d j = D (j + 1) - D j := by intro j; simp [hD, sum_range_succ]
  have hC' : ∑ i ∈ range m, (D (i + 1) - D i) * e i ≤ 0 := by
    have h1 : ∑ i ∈ range m, d i * e i =
        ∑ i : Fin m, (κ₀ i - κ i) * (κ₀ i + κ i + m - 1 - 2 * (i : ℕ)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => d i * e i) m]
      refine sum_congr rfl (fun i _ => ?_)
      simp [hd, he, i.isLt]
    have h2 : ∑ i : Fin m, (κ₀ i - κ i) * (κ₀ i + κ i + m - 1 - 2 * (i : ℕ)) =
        ∑ i, κ₀ i * (κ₀ i + m - 1 - 2 * (i : ℕ)) - ∑ i, κ i * (κ i + m - 1 - 2 * (i : ℕ)) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl (fun i _ => ?_)
      ring
    simp_rw [← hdD]
    rw [h1, h2]
    linarith
  have key := sum_range_sub_mul_eq_abel_summation D e m
  rw [hDm, hDzero, zero_mul, zero_mul, zero_add, sub_zero] at key
  have he_gap : ∀ i, i + 1 < m → 2 ≤ e i - e (i + 1) := by
    intro i hi
    have h1 := h₀ (Fin.mk_le_mk.mpr (Nat.le_succ i) : (⟨i, by omega⟩ : Fin m) ≤ ⟨i + 1, hi⟩)
    have h2 := h (Fin.mk_le_mk.mpr (Nat.le_succ i) : (⟨i, by omega⟩ : Fin m) ≤ ⟨i + 1, hi⟩)
    simp only [he, hi, show i < m by omega, ↓reduceDIte]
    push_cast
    linarith
  have hterm : ∀ i ∈ range m, 0 ≤ D (i + 1) * (e i - e (i + 1)) := by
    intro i hi
    rw [mem_range] at hi
    rcases Nat.lt_or_ge (i + 1) m with h' | h'
    · exact mul_nonneg (hD0 _) (by linarith [he_gap i h'])
    · rw [show i + 1 = m by omega, hDm, zero_mul]
  have hsum0 : ∑ i ∈ range m, D (i + 1) * (e i - e (i + 1)) = 0 :=
    le_antisymm (by linarith) (sum_nonneg hterm)
  have hall := (sum_eq_zero_iff_of_nonneg hterm).mp hsum0
  have hDall : ∀ j, j ≤ m → D j = 0 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hDzero
    rcases Nat.lt_or_ge j m with hjm | hjm
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rcases mul_eq_zero.mp (hall i (mem_range.mpr (by omega))) with h0 | h0
      · exact h0
      · linarith [he_gap i hjm]
    · rw [show j = m by omega]
      exact hDm
  funext k
  have hk' := k.isLt
  have hk := hdD k
  rw [hDall ((k : ℕ) + 1) (by omega), hDall (k : ℕ) (by omega)] at hk
  simp [hd, k.isLt] at hk
  linarith
end _root_.GlobalTheory.Harm
end GlobalTheory.Harm
