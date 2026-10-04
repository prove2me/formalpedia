-- Prove2me | solution 1 for MDPFinance.OptimalStopping.theorem_10_3_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:28:52.834991+00:00
-- url     : https://prove2.me/submissions/c907e90a-b244-4678-8f6c-330e341a2a39

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Applications

open MeasureTheory Finset Filter Topology MDPFinance.OptimalStopping

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


theorem W_ge (S : Secretary) (j x : ℕ) : (x : ℝ) / S.N ≤ S.W j x := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact le_max_left _ _

theorem W_gt (S : Secretary) (j x : ℕ) (hj : 1 ≤ j) (hx1 : 1 ≤ x) (hxk : x ≤ S.kStar) :
    (x : ℝ) / S.N < S.W j x := by
  obtain ⟨hk, hkh, _⟩ := kstar_spec S
  have hkN : S.kStar ≤ S.N - 2 := (Finset.mem_Icc.mp hk).2
  have hN3 := S.N_ge
  have hNpos : (0 : ℝ) < S.N := by positivity
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Secretary.W]
  refine lt_of_lt_of_le ?_ (le_max_right _ _)
  rw [Finset.Icc_add_one_left_eq_Ioc]
  have hle : (x : ℝ) / S.N * ∑ y ∈ Ioc x S.N, (1 : ℝ) / ((y : ℝ) - 1) ≤
      ∑ y ∈ Ioc x S.N, ((x : ℝ) / ((y : ℝ) * ((y : ℝ) - 1))) * S.W j y := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y hy => ?_
    simp only [Finset.mem_Ioc] at hy
    have hy1 : (1 : ℝ) < y := by exact_mod_cast (by omega : 1 < y)
    have hw := W_ge S j y
    have e : (x : ℝ) / S.N * (1 / ((y : ℝ) - 1)) =
        ((x : ℝ) / ((y : ℝ) * ((y : ℝ) - 1))) * ((y : ℝ) / S.N) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hw (by positivity)
  refine lt_of_lt_of_le ?_ hle
  rw [reindex x S.N (by omega)]
  have hh : 1 < secretaryH S.N x := lt_of_lt_of_le hkh (h_anti S.N x S.kStar hxk)
  unfold secretaryH at hh
  have hx0 : (0 : ℝ) < (x : ℝ) / S.N := by
    have : (1 : ℝ) ≤ x := by exact_mod_cast hx1
    positivity
  nlinarith

theorem log_lower (k : ℕ) (hk : 1 ≤ k) : ∀ N, k ≤ N →
    Real.log ((N : ℝ) / k) ≤ secretaryH N k := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
    have : (k : ℝ) ≠ 0 := by positivity
    simp [secretaryH, this]
  | succ N hkN ih =>
    unfold secretaryH at ih ⊢
    rw [Finset.sum_Ico_succ_top hkN]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hk hkN)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have e : Real.log (((N + 1 : ℕ) : ℝ) / k) = Real.log ((N : ℝ) / k) + Real.log ((N + 1) / N) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      push_cast
      field_simp
    rw [e]
    have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (N + 1) / N by positivity)
    have : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
    linarith

theorem log_upper (k : ℕ) (hk : 2 ≤ k) : ∀ N, k ≤ N →
    secretaryH N k ≤ Real.log (((N : ℝ) - 1) / ((k : ℝ) - 1)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
    have : (k : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    simp [secretaryH, this]
  | succ N hkN ih =>
    unfold secretaryH at ih ⊢
    rw [Finset.sum_Ico_succ_top hkN]
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (le_trans hk hkN)
    have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    have e : Real.log ((((N + 1 : ℕ) : ℝ) - 1) / ((k : ℝ) - 1)) =
        Real.log (((N : ℝ) - 1) / ((k : ℝ) - 1)) + Real.log ((N : ℝ) / ((N : ℝ) - 1)) := by
      rw [← Real.log_mul (div_pos hN1 hk1).ne' (div_pos (by linarith) hN1).ne']
      congr 1
      push_cast
      field_simp
      ring
    rw [e]
    have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) - 1) / N by
      have : (0:ℝ) < (N:ℝ) - 1 := by linarith
      positivity)
    have hinv : Real.log ((N : ℝ) / ((N : ℝ) - 1)) = -Real.log (((N : ℝ) - 1) / N) := by
      rw [← Real.log_inv, inv_div]
    have : ((N : ℝ) - 1) / N - 1 = -(1 / N) := by
      have : (N : ℝ) ≠ 0 := by linarith
      field_simp; ring
    linarith

/-- the bounds `1/e - 1/N ≤ k*/N < 1/e + 1/N` for large `N`. -/
theorem kstar_bounds (N : ℕ) (hN : 6 ≤ N) :
    |(secretaryKStar N : ℝ) / N - 1 / Real.exp 1| ≤ 1 / N := by
  let S : Secretary := ⟨N, by omega⟩
  have hK : secretaryKStar N = S.kStar := rfl
  obtain ⟨hk, hkh, hk2⟩ := kstar_spec S
  have hk1 : 1 ≤ S.kStar := (Finset.mem_Icc.mp hk).1
  have hkN : S.kStar ≤ N - 2 := (Finset.mem_Icc.mp hk).2
  have hNpos : (0 : ℝ) < N := by positivity
  have hN6 : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  -- lower bound from `h(k*+1) ≤ 1`
  have hlow := (log_lower (S.kStar + 1) (by omega) N (by omega)).trans hk2
  have hk10 : (0 : ℝ) < ((S.kStar + 1 : ℕ) : ℝ) := by positivity
  rw [Real.log_le_iff_le_exp (by positivity), div_le_iff₀ hk10] at hlow
  -- `k* ≥ 2`
  have hk2' : 2 ≤ S.kStar := by
    by_contra hlt
    have h1 : S.kStar = 1 := by omega
    have := (log_lower 2 (by norm_num) N (by omega)).trans (h1 ▸ hk2)
    rw [Real.log_le_iff_le_exp (by positivity), div_le_iff₀ (by norm_num)] at this
    have he3 := Real.exp_one_lt_d9
    push_cast at this
    linarith
  -- upper bound from `h(k*) > 1`
  have hup := lt_of_lt_of_le hkh (log_upper S.kStar hk2' N (by omega))
  have hkm : (0 : ℝ) < (S.kStar : ℝ) - 1 := by
    have : (2 : ℝ) ≤ S.kStar := by exact_mod_cast hk2'
    linarith
  rw [Real.lt_log_iff_exp_lt (by
    have : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    positivity), lt_div_iff₀ hkm] at hup
  rw [hK, abs_le]
  push_cast at hlow
  have hrw : (S.kStar : ℝ) / N - 1 / Real.exp 1 =
      ((S.kStar : ℝ) * Real.exp 1 - N) / (N * Real.exp 1) := by
    field_simp
  rw [hrw]
  have hNe : (0 : ℝ) < N * Real.exp 1 := by positivity
  constructor
  · rw [le_div_iff₀ hNe]
    have : -(1 / (N : ℝ)) * (N * Real.exp 1) = -Real.exp 1 := by field_simp
    rw [this]
    nlinarith
  · rw [div_le_iff₀ hNe]
    have : 1 / (N : ℝ) * (N * Real.exp 1) = Real.exp 1 := by field_simp
    rw [this]
    nlinarith

end SecAux

open SecAux in
theorem solution (S : Secretary) :
    (∀ n : ℕ, n ≤ S.kStar →
      {x : ℕ | x ∈ Finset.Icc 1 S.N ∧ S.V n x = S.g x} =
        {x : ℕ | x ∈ Finset.Icc 1 S.N ∧ S.kStar < x}) ∧
    S.V 0 1 = ((S.kStar : ℝ) / (S.N : ℝ)) * S.h S.kStar ∧
    Tendsto (fun N : ℕ => (secretaryKStar N : ℝ) / (N : ℝ)) atTop (𝓝 (1 / Real.exp 1)) := by
  obtain ⟨hk, hkh, hk2⟩ := kstar_spec S
  have hk1 : 1 ≤ S.kStar := (Finset.mem_Icc.mp hk).1
  have hkN : S.kStar ≤ S.N - 2 := (Finset.mem_Icc.mp hk).2
  have hN3 := S.N_ge
  refine ⟨fun n hn => ?_, W_low S _ 1 le_rfl hk1 (by omega), ?_⟩
  · ext x
    simp only [Set.mem_setOf_eq, Finset.mem_Icc]
    constructor
    · rintro ⟨hx, hV⟩
      refine ⟨hx, ?_⟩
      by_contra hle
      push_neg at hle
      have hg : S.g x = (x : ℝ) / S.N := by
        unfold Secretary.g; rw [if_neg (by omega)]
      have := W_gt S (S.N - 1 - n) x (by omega) hx.1 hle
      unfold Secretary.V at hV
      rw [hV, hg] at this
      exact lt_irrefl _ this
    · rintro ⟨hx, hlt⟩
      refine ⟨hx, ?_⟩
      have hg : S.g x = (x : ℝ) / S.N := by
        unfold Secretary.g; rw [if_neg (by omega)]
      rw [hg]
      exact W_high S _ x (by omega) hx.2
  · have hlim : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop 6] with N hN
    rw [Real.norm_eq_abs]
    exact kstar_bounds N hN

#print axioms solution
