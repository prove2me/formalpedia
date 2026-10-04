-- Prove2me | solution 1 for MDPFinance.OptimalStopping.proposition_10_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:26:53.221834+00:00
-- url     : https://prove2.me/submissions/9b2ceb8d-6b45-4b9f-add5-56366c69ee07

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Applications

open MeasureTheory Finset MDPFinance.OptimalStopping

namespace SecAux

/-- telescoping: `∑_{y=x+1}^{k} 1/(y(y-1)) = 1/x - 1/k`. -/
theorem telescope (x : ℕ) (hx : 1 ≤ x) : ∀ k, x ≤ k →
    ∑ y ∈ Ioc x k, (1 : ℝ) / ((y : ℝ) * ((y : ℝ) - 1)) = 1 / (x : ℝ) - 1 / (k : ℝ) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hxk ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (le_trans hx hxk)
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hx0 : (x : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ x := by exact_mod_cast hx
                                 positivity
    have hk10 : (k : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    rw [show ((k : ℝ) + 1 - 1) = k by ring]
    field_simp
    ring

/-- reindexing: `∑_{y=a+1}^{N} 1/(y-1) = ∑_{j=a}^{N-1} 1/j`. -/
theorem reindex (a : ℕ) : ∀ N, a ≤ N →
    ∑ y ∈ Ioc a N, (1 : ℝ) / ((y : ℝ) - 1) = ∑ j ∈ Ico a N, (1 : ℝ) / (j : ℝ) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N haN ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ico_succ_top haN, ih]
    push_cast
    ring_nf

theorem h_anti (N a b : ℕ) (hab : a ≤ b) : secretaryH N b ≤ secretaryH N a := by
  unfold secretaryH
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_Ico] at hj ⊢
    omega
  · intro j _ _
    positivity

theorem h_last (S : Secretary) : secretaryH S.N (S.N - 2 + 1) ≤ 1 := by
  have hN := S.N_ge
  unfold secretaryH
  rw [show S.N - 2 + 1 = S.N - 1 by omega]
  have e : Ico (S.N - 1) S.N = {S.N - 1} := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [e, Finset.sum_singleton]
  have : (1 : ℝ) ≤ ((S.N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ S.N - 1)
  rw [div_le_one (by linarith)]
  exact this

theorem kstar_spec (S : Secretary) :
    S.kStar ∈ Finset.Icc 1 (S.N - 2) ∧ 1 < S.h S.kStar ∧ S.h (S.kStar + 1) ≤ 1 := by
  have hN := S.N_ge
  have hex : ∃ k, secretaryH S.N (k + 1) ≤ 1 := ⟨S.N - 2, h_last S⟩
  classical
  let k1 := Nat.find hex
  have hk1 : secretaryH S.N (k1 + 1) ≤ 1 := Nat.find_spec hex
  have hk1le : k1 ≤ S.N - 2 := Nat.find_min' hex (h_last S)
  have h1 : 1 < secretaryH S.N 1 := by
    unfold secretaryH
    have hsub : ({1, 2} : Finset ℕ) ⊆ Ico 1 S.N := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      simp only [Finset.mem_Ico]
      omega
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun j : ℕ => (1 : ℝ) / (j : ℝ)) (fun j _ _ => by positivity)
    rw [Finset.sum_pair (by norm_num)] at this
    norm_num at this
    simp only [one_div] at *
    linarith
  have hk1pos : 1 ≤ k1 := by
    by_contra h
    have : k1 = 0 := by omega
    rw [this] at hk1
    linarith
  have hk1h : 1 < secretaryH S.N k1 := by
    have hmin := Nat.find_min hex (show k1 - 1 < k1 by omega)
    rw [show k1 - 1 + 1 = k1 by omega] at hmin
    exact lt_of_not_ge hmin
  have hmem : k1 ∈ {k : ℕ | k ∈ Finset.Icc 1 (S.N - 2) ∧ 1 < secretaryH S.N k ∧
      secretaryH S.N (k + 1) ≤ 1} :=
    ⟨Finset.mem_Icc.mpr ⟨hk1pos, hk1le⟩, hk1h, hk1⟩
  exact Nat.sInf_mem ⟨k1, hmem⟩

theorem W_top (S : Secretary) (j : ℕ) : S.W j S.N = 1 := by
  have hN : (S.N : ℝ) ≠ 0 := by have := S.N_ge; positivity
  cases j with
  | zero => simp [Secretary.W, hN]
  | succ j =>
    simp only [Secretary.W, div_self hN]
    rw [show Icc (S.N + 1) S.N = ∅ by ext y; simp, Finset.sum_empty]
    simp

theorem W_high (S : Secretary) (j : ℕ) : ∀ x, S.kStar + 1 ≤ x → x ≤ S.N →
    S.W j x = (x : ℝ) / (S.N : ℝ) := by
  obtain ⟨hk, _, hk2⟩ := kstar_spec S
  have hk1 : 1 ≤ S.kStar := (Finset.mem_Icc.mp hk).1
  have hNpos : (0 : ℝ) < S.N := by have := S.N_ge; positivity
  induction j with
  | zero => intro x _ _; rfl
  | succ j ih =>
    intro x hx1 hxN
    simp only [Secretary.W]
    apply max_eq_left
    have hsum : ∑ y ∈ Ioc x S.N, ((x : ℝ) / ((y : ℝ) * ((y : ℝ) - 1))) * S.W j y =
        (x : ℝ) / S.N * ∑ y ∈ Ioc x S.N, (1 : ℝ) / ((y : ℝ) - 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      simp only [Finset.mem_Ioc] at hy
      rw [ih y (by omega) hy.2]
      have hy1 : (1 : ℝ) < y := by exact_mod_cast (by omega : 1 < y)
      field_simp
    rw [Finset.Icc_add_one_left_eq_Ioc, hsum, reindex x S.N hxN]
    have hh : secretaryH S.N x ≤ 1 := (h_anti S.N (S.kStar + 1) x hx1).trans hk2
    unfold secretaryH at hh
    have hx0 : (0 : ℝ) ≤ (x : ℝ) / S.N := by positivity
    nlinarith

theorem W_low (S : Secretary) (j : ℕ) : ∀ x, 1 ≤ x → x ≤ S.kStar → S.N - 1 - x ≤ j →
    S.W j x = ((S.kStar : ℝ) / (S.N : ℝ)) * S.h S.kStar := by
  obtain ⟨hk, hkh, hk2⟩ := kstar_spec S
  have hk1 : 1 ≤ S.kStar := (Finset.mem_Icc.mp hk).1
  have hkN : S.kStar ≤ S.N - 2 := (Finset.mem_Icc.mp hk).2
  have hN3 := S.N_ge
  have hNpos : (0 : ℝ) < S.N := by positivity
  induction j with
  | zero => intro x _ hx hj; omega
  | succ j ih =>
    intro x hx1 hxk hj
    simp only [Secretary.W]
    rw [Finset.Icc_add_one_left_eq_Ioc,
      ← Finset.sum_Ioc_consecutive _ hxk (by omega : S.kStar ≤ S.N)]
    have hA : ∑ y ∈ Ioc x S.kStar, ((x : ℝ) / ((y : ℝ) * ((y : ℝ) - 1))) * S.W j y =
        (x : ℝ) * ((S.kStar : ℝ) / S.N * S.h S.kStar) *
          ∑ y ∈ Ioc x S.kStar, (1 : ℝ) / ((y : ℝ) * ((y : ℝ) - 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      simp only [Finset.mem_Ioc] at hy
      rw [ih y (by omega) hy.2 (by omega)]
      ring
    have hB : ∑ y ∈ Ioc S.kStar S.N, ((x : ℝ) / ((y : ℝ) * ((y : ℝ) - 1))) * S.W j y =
        (x : ℝ) / S.N * ∑ y ∈ Ioc S.kStar S.N, (1 : ℝ) / ((y : ℝ) - 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      simp only [Finset.mem_Ioc] at hy
      rw [W_high S j y (by omega) hy.2]
      have hy1 : (1 : ℝ) < y := by exact_mod_cast (by omega : 1 < y)
      field_simp
    rw [hA, hB, telescope x hx1 S.kStar hxk, reindex S.kStar S.N (by omega)]
    have hhdef : S.h S.kStar = ∑ j ∈ Ico S.kStar S.N, (1 : ℝ) / (j : ℝ) := rfl
    rw [← hhdef]
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
    have hk0 : (0 : ℝ) < S.kStar := by exact_mod_cast hk1
    have hxk' : (x : ℝ) ≤ S.kStar := by exact_mod_cast hxk
    have e : (x : ℝ) * ((S.kStar : ℝ) / S.N * S.h S.kStar) * (1 / (x : ℝ) - 1 / (S.kStar : ℝ)) +
        (x : ℝ) / S.N * S.h S.kStar = (S.kStar : ℝ) / S.N * S.h S.kStar := by
      field_simp
      ring
    rw [e]
    apply max_eq_right
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hNpos]
    nlinarith

end SecAux

open SecAux in
theorem solution (S : Secretary) (n : ℕ) (hn : n < S.N) :
    (S.V n S.N = 1) ∧
    (∀ x : ℕ, S.kStar + 1 ≤ x → x ≤ S.N - 1 → S.V n x = (x : ℝ) / (S.N : ℝ)) ∧
    (∀ x : ℕ, 1 ≤ x → n ≤ x → x ≤ S.kStar →
      S.V n x = ((S.kStar : ℝ) / (S.N : ℝ)) * S.h S.kStar) := by
  refine ⟨W_top S _, fun x hx1 hx2 => W_high S _ x hx1 (by omega),
    fun x hx1 hnx hxk => W_low S _ x hx1 hxk (by omega)⟩

#print axioms solution
