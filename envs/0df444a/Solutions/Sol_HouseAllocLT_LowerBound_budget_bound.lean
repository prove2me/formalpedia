-- Prove2me | solution 1 for HouseAllocLT.LowerBound.budget_bound
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:00:00.801133+00:00
-- url     : https://prove2.me/submissions/f2fde41a-a262-4dbe-84e9-64c119e3d638

import Definitions.Def_HouseAllocLT_LowerBound_prefixList

set_option autoImplicit false

open scoped BigOperators ENNReal Topology
open Filter

open HouseAllocLT.LowerBound

private lemma bb_t_lt {n : ℕ} (hn : 2 ≤ n) : t n < n := by
  have h : t n ≤ n - 1 := by
    unfold t
    apply Finset.sup_le
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [id]
    omega
  omega

private lemma bb_harm (n : ℕ) : ∀ k, k ≤ n →
    (∑ j ∈ Finset.range k, (1 : ℝ) / ((n - j : ℕ) : ℝ)) =
      (harmonic n : ℝ) - (harmonic (n - k) : ℝ) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [Finset.sum_range_succ, ih (by omega)]
    obtain ⟨m, hm1, hm2⟩ : ∃ m, n - k = m + 1 ∧ n - (k + 1) = m := ⟨n - (k + 1), by omega, rfl⟩
    rw [hm1, hm2, harmonic_succ]
    push_cast
    ring

private lemma bb_term {n τ : ℕ} (j : ℕ) (hj : j < n) (hτ : τ ≤ n) (x : ℝ) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1 / ((n - j : ℕ) : ℝ)) :
    ((n - j : ℕ) : ℝ) * x ≤ ((n - τ : ℕ) : ℝ) * x +
      (if j < τ then 1 - ((n - τ : ℕ) : ℝ) / ((n - j : ℕ) : ℝ) else 0) := by
  have ha : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - j)
  split_ifs with h
  · have hca : ((n - τ : ℕ) : ℝ) ≤ ((n - j : ℕ) : ℝ) := by exact_mod_cast (by omega : n - τ ≤ n - j)
    have key : (((n - j : ℕ) : ℝ) - ((n - τ : ℕ) : ℝ)) * x ≤
        (((n - j : ℕ) : ℝ) - ((n - τ : ℕ) : ℝ)) * (1 / ((n - j : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hx1 (by linarith)
    have e : (((n - j : ℕ) : ℝ) - ((n - τ : ℕ) : ℝ)) * (1 / ((n - j : ℕ) : ℝ)) =
        1 - ((n - τ : ℕ) : ℝ) / ((n - j : ℕ) : ℝ) := by field_simp
    linarith
  · have hca : ((n - j : ℕ) : ℝ) ≤ ((n - τ : ℕ) : ℝ) := by exact_mod_cast (by omega : n - j ≤ n - τ)
    nlinarith

theorem solution {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1 / ((n - j.val : ℕ) : ℝ))
    (hsum : (∑ j, x j) ≤ 1) :
    (∑ j, ((n - j.val : ℕ) : ℝ) * x j) ≤ B n := by
  set τ := t n with hτdef
  have hτ : τ < n := bb_t_lt hn
  set c : ℝ := ((n - τ : ℕ) : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  let g : ℕ → ℝ := fun j => if j < τ then 1 - c / ((n - j : ℕ) : ℝ) else 0
  have h1 : (∑ j : Fin n, ((n - j.val : ℕ) : ℝ) * x j) ≤ ∑ j : Fin n, (c * x j + g j.val) :=
    Finset.sum_le_sum (fun j _ => bb_term j.val j.isLt hτ.le (x j) (hx j).1 (hx j).2)
  have h2 : (∑ j : Fin n, g j.val) = τ - c * ((harmonic n : ℝ) - (harmonic (n - τ) : ℝ)) := by
    rw [Fin.sum_univ_eq_sum_range g n]
    simp only [g]
    rw [← Finset.sum_filter]
    have hf : (Finset.range n).filter (fun j => j < τ) = Finset.range τ := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hf, Finset.sum_sub_distrib, ← bb_harm n τ hτ.le, Finset.mul_sum]
    simp [div_eq_mul_inv]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, h2] at h1
  have h3 : c * (∑ j, x j) ≤ c := by nlinarith
  unfold B
  rw [if_pos hn]
  unfold J
  rw [← hτdef]
  nlinarith
