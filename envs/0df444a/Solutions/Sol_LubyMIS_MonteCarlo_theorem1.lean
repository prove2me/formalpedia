-- Prove2me | solution 1 for LubyMIS.MonteCarlo.theorem1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T15:00:01.815989+00:00
-- url     : https://prove2.me/submissions/df20a824-cd82-4767-89c8-b5f4cb98fe1e

import Theorems.Thm_LubyMIS_MonteCarlo_lemmaA
import Theorems.Thm_LubyMIS_MonteCarlo_lemmaB
import Theorems.Thm_LubyMIS_MonteCarlo_eliminated_ge_half_degree_sum
import Theorems.Thm_LubyMIS_MonteCarlo_degree_sum_ge_edges

/-!
Luby (1986), Theorem 1, pp. 1040--1041. The four imported milestones are
existing accepted proofs by mrfancypants. This file supplies the final
expectation, truncation, and finite-priority error estimates.
-/

open Classical Finset LubyMIS.MonteCarlo

namespace LubyTheoremOne

private lemma expA_ge_degree {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (hn : 1 ≤ n) (H : SimpleGraph V) [DecidableRel H.Adj] :
    1 / 2 * ∑ i, (H.degree i : ℝ) * probA n (fun π => i ∈ nbhd H (selectA H π)) ≤
      expA n (fun π => (eliminated H (selectA H π) : ℝ)) := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let D : ℝ := ((n : ℝ) ^ 4) ^ Fintype.card V
  have hD : 0 < D := by dsimp [D]; positivity
  have hcard : (Fintype.card (V → Fin (n ^ 4)) : ℝ) = D := by
    simp [D]
  have hw : (∑ _ : V → Fin (n ^ 4), 1 / D) = (1 : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcard]
    field_simp
  have he := eliminated_ge_half_degree_sum H (fun _ : V → Fin (n ^ 4) => 1 / D)
    (fun _ => by positivity) hw (fun π₀ => selectA H (prioA π₀))
  have h := he.2.trans he.1
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at h
  have hexp : (∑ π₀ : V → Fin (n ^ 4),
      1 / D * (eliminated H (selectA H (prioA π₀)) : ℝ)) =
      expA n (fun π => (eliminated H (selectA H π) : ℝ)) := by
    unfold expA
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro π₀ _
    dsimp [D]
    ring
  rw [hexp] at h
  simpa only [probA, D, div_eq_mul_inv, one_mul] using h

private lemma lawB_nonneg {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (c : V → Bool) : 0 ≤ lawB H c := by
  unfold lawB
  apply Finset.prod_nonneg
  intro i _
  have hp0 : 0 ≤ coinProb H i := by
    unfold coinProb
    split_ifs <;> positivity
  have hp1 : coinProb H i ≤ 1 := by
    unfold coinProb
    split_ifs with hi
    · have hd : (1 : ℝ) ≤ H.degree i := by exact_mod_cast hi
      rw [div_le_one (by positivity)]
      linarith
    · exact le_rfl
  split_ifs <;> linarith

private lemma lawB_sum {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : ∑ c : V → Bool, lawB H c = 1 := by
  unfold lawB
  rw [← Fintype.prod_sum (fun i (b : Bool) => if b then coinProb H i else 1 - coinProb H i)]
  simp

private lemma expB_ge_degree {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    1 / 2 * ∑ i, (H.degree i : ℝ) * probB H (fun c => i ∈ nbhd H (selectB H c)) ≤
      expB H (fun c => (eliminated H (selectB H c) : ℝ)) := by
  classical
  have he := eliminated_ge_half_degree_sum H (lawB H) (lawB_nonneg H) (lawB_sum H)
    (selectB H)
  have hp (i : V) : probB H (fun c => i ∈ nbhd H (selectB H c)) =
      ∑ c : V → Bool, if i ∈ nbhd H (selectB H c) then lawB H c else 0 := by
    unfold probB
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : i ∈ nbhd H (selectB H c) <;> simp [hc]
  simpa only [hp, expB] using he.2.trans he.1

private lemma truncated_degree_ge_edges {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    (H.edgeFinset.card : ℝ) ≤ ∑ i, (H.degree i : ℝ) * min (sumInv H i / 2) 1 := by
  classical
  calc
    (H.edgeFinset.card : ℝ) ≤
        (∑ i ∈ Finset.univ.filter (fun i => sumInv H i ≤ 2),
          (H.degree i : ℝ) * sumInv H i / 2) +
        (∑ i ∈ Finset.univ.filter (fun i => 2 < sumInv H i), (H.degree i : ℝ)) :=
      degree_sum_ge_edges H
    _ = ∑ i, (H.degree i : ℝ) * min (sumInv H i / 2) 1 := by
      simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hs : sumInv H i ≤ 2
      · rw [if_pos hs, if_neg (not_lt.mpr hs), min_eq_left (by linarith)]
        ring
      · rw [if_neg hs, if_pos (lt_of_not_ge hs), min_eq_right (by linarith)]
        ring

end LubyTheoremOne

open LubyTheoremOne

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (hn : 1 ≤ n)
    (hV : Fintype.card V ≤ n) (H : SimpleGraph V) [DecidableRel H.Adj] :
    expA n (fun π => (eliminated H (selectA H π) : ℝ)) ≥
        1 / 8 * (H.edgeFinset.card : ℝ) - 1 / 16 ∧
      expB H (fun c => (eliminated H (selectB H c) : ℝ)) ≥ 1 / 8 * (H.edgeFinset.card : ℝ) := by
  classical
  have hcharge := truncated_degree_ge_edges H
  have hnonneg (i : V) : 0 ≤ sumInv H i := by
    unfold sumInv
    positivity
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  let q : ℝ := 1 - 1 / (2 * (n : ℝ) ^ 2)
  have hq : 0 ≤ q := by
    dsimp [q]
    have : 1 / (2 * (n : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  have hA : 1 / 8 * (H.edgeFinset.card : ℝ) * q ≤
      expA n (fun π => (eliminated H (selectA H π) : ℝ)) := by
    calc
      _ ≤ 1 / 8 * (∑ i, (H.degree i : ℝ) * min (sumInv H i / 2) 1) * q := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcharge (by norm_num)) hq
      _ = 1 / 2 * ∑ i, (H.degree i : ℝ) *
          ((1 / 4 * min (sumInv H i / 2) 1) * q) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ 1 / 2 * ∑ i, (H.degree i : ℝ) *
          probA n (fun π => i ∈ nbhd H (selectA H π)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : 1 ≤ H.degree i
        · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          have hmin : min (sumInv H i / 2) 1 ≤ min (sumInv H i) 1 :=
            min_le_min_right _ (by nlinarith [hnonneg i])
          exact (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmin (by norm_num)) hq).trans (lemmaA n hn hV H i hi)
        · have hd : H.degree i = 0 := by omega
          simp [hd]
      _ ≤ _ := expA_ge_degree n hn H
  have hB : 1 / 8 * (H.edgeFinset.card : ℝ) ≤
      expB H (fun c => (eliminated H (selectB H c) : ℝ)) := by
    calc
      _ ≤ 1 / 8 * (∑ i, (H.degree i : ℝ) * min (sumInv H i / 2) 1) :=
        mul_le_mul_of_nonneg_left hcharge (by norm_num)
      _ = 1 / 2 * ∑ i, (H.degree i : ℝ) * (1 / 4 * min (sumInv H i / 2) 1) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ 1 / 2 * ∑ i, (H.degree i : ℝ) *
          probB H (fun c => i ∈ nbhd H (selectB H c)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : 1 ≤ H.degree i
        · exact mul_le_mul_of_nonneg_left (lemmaB H i hi) (Nat.cast_nonneg _)
        · have hd : H.degree i = 0 := by omega
          simp [hd]
      _ ≤ _ := expB_ge_degree H
  refine ⟨?_, hB⟩
  have hdeg : ∑ i, H.degree i ≤ n * n := by
    calc
      _ ≤ ∑ _ : V, n := by
        apply Finset.sum_le_sum
        intro i _
        exact (H.degree_lt_card_verts i).le.trans hV
      _ = Fintype.card V * n := by simp
      _ ≤ n * n := Nat.mul_le_mul_right n hV
  have hE : (H.edgeFinset.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [H.sum_degrees_eq_twice_card_edges] at hdeg
    have : (2 : ℝ) * H.edgeFinset.card ≤ (n : ℝ) * n := by exact_mod_cast hdeg
    nlinarith [Nat.cast_nonneg (α := ℝ) H.edgeFinset.card]
  have herr : (H.edgeFinset.card : ℝ) / (16 * (n : ℝ) ^ 2) ≤ 1 / 16 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hid : 1 / 8 * (H.edgeFinset.card : ℝ) * q =
      1 / 8 * (H.edgeFinset.card : ℝ) -
        (H.edgeFinset.card : ℝ) / (16 * (n : ℝ) ^ 2) := by
    dsimp [q]
    ring
  rw [hid] at hA
  linarith
