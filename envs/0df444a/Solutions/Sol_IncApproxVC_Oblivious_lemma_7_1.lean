-- Prove2me | solution 1 for IncApproxVC.Oblivious.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-19T15:57:17.093973+00:00
-- url     : https://prove2.me/submissions/91c9422e-e791-4aec-8469-646155432d4d

import Mathlib

open Finset
open scoped BigOperators

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (k : ℝ) (hk : 1 ≤ k)
    (A : Finset V) (hA : k ≤ (A.card : ℝ)) :
    ((Finset.univ.filter (fun σ : Fin ⌈10 * ((Fintype.card V : ℝ) / k) *
          Real.logb 2 (Fintype.card V)⌉₊ → V => ∃ j, σ j ∈ A)).card : ℝ) /
        (Fintype.card (Fin ⌈10 * ((Fintype.card V : ℝ) / k) *
          Real.logb 2 (Fintype.card V)⌉₊ → V) : ℝ) ≥
      1 - (Fintype.card V : ℝ) ^ (-10 : ℝ) := by
  classical
  set n : ℕ := Fintype.card V with hndef
  set N : ℕ := ⌈10 * ((Fintype.card V : ℝ) / k) * Real.logb 2 (Fintype.card V)⌉₊ with hNdef
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hAcard_le : A.card ≤ n := by
    rw [hndef]; exact A.card_le_univ
  have hA_le_n : k ≤ (n : ℝ) := by
    have h1 : (A.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hAcard_le
    linarith
  have hn1 : 1 ≤ n := by
    have h1 : (0 : ℝ) < (A.card : ℝ) := lt_of_lt_of_le zero_lt_one (le_trans hk hA)
    have h2 : 0 < A.card := by exact_mod_cast h1
    omega
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnr
  -- counting: number of sequences missing A
  have hcount_sub : Fintype.card {σ : Fin N → V // ∀ j, σ j ∉ A}
      = (Finset.univ.filter (fun σ : Fin N → V => ∀ j, σ j ∉ A)).card :=
    Fintype.card_subtype (fun σ : Fin N → V => ∀ j, σ j ∉ A)
  have hcard_avoid : (Finset.univ.filter (fun σ : Fin N → V => ∀ j, σ j ∉ A)).card
      = (n - A.card) ^ N := by
    rw [← hcount_sub]
    rw [Fintype.card_congr (Equiv.subtypePiEquivPi (β := fun (_ : Fin N) => V)
      (p := fun (_ : Fin N) (v : V) => v ∉ A))]
    rw [Fintype.card_pi_const]
    congr 1
    rw [Fintype.card_subtype_compl (fun v : V => v ∈ A), hndef, Fintype.card_coe]
  -- the hit set is the complement of the avoid set
  have hsplit : (Finset.univ.filter (fun σ : Fin N → V => ∃ j, σ j ∈ A)).card +
      (Finset.univ.filter (fun σ : Fin N → V => ∀ j, σ j ∉ A)).card = n ^ N := by
    have hfilter : (Finset.univ.filter (fun σ : Fin N → V => ∀ j, σ j ∉ A))
        = Finset.univ.filter (fun σ : Fin N → V => ¬ ∃ j, σ j ∈ A) := by
      apply Finset.filter_congr
      intro σ _
      simp only [not_exists]
    rw [hfilter, Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_pi_const, ← hndef]
  have hle_avoid : (Finset.univ.filter (fun σ : Fin N → V => ∀ j, σ j ∉ A)).card ≤ n ^ N := by
    omega
  have hhit_sub : (Finset.univ.filter (fun σ : Fin N → V => ∃ j, σ j ∈ A)).card
      = n ^ N - (Finset.univ.filter (fun σ : Fin N → V => ∀ j, σ j ∉ A)).card := by
    omega
  have hhit : ((Finset.univ.filter (fun σ : Fin N → V => ∃ j, σ j ∈ A)).card : ℝ)
      = (n : ℝ) ^ N - ((Finset.univ.filter (fun σ : Fin N → V => ∀ j, σ j ∉ A)).card : ℝ) := by
    rw [hhit_sub, Nat.cast_sub hle_avoid, Nat.cast_pow]
  have htotal : (Fintype.card (Fin N → V) : ℝ) = (n : ℝ) ^ N := by
    rw [Fintype.card_pi_const, ← hndef, Nat.cast_pow]
  -- ratio of avoiding sequences
  have hratio : ((Finset.univ.filter (fun σ : Fin N → V => ∀ j, σ j ∉ A)).card : ℝ) /
        (n : ℝ) ^ N = (((n : ℝ) - (A.card : ℝ)) / (n : ℝ)) ^ N := by
    rw [hcard_avoid, Nat.cast_pow, Nat.cast_sub hAcard_le, div_pow]
  -- bound by (1 - k/n)^N
  have hstep1 : (((n : ℝ) - (A.card : ℝ)) / (n : ℝ)) ^ N
      ≤ (((n : ℝ) - k) / (n : ℝ)) ^ N := by
    apply pow_le_pow_left₀
    · apply div_nonneg
      · have h1 : (A.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hAcard_le
        linarith
      · linarith
    · apply div_le_div_of_nonneg_right _ (le_of_lt hnr)
      linarith
  have hstep2 : (((n : ℝ) - k) / (n : ℝ)) ^ N = (1 - k / (n : ℝ)) ^ N := by
    have h1 : ((n : ℝ) - k) / (n : ℝ) = 1 - k / (n : ℝ) := by
      field_simp
    rw [h1]
  -- exponential bound
  have hstep3 : (1 - k / (n : ℝ)) ^ N ≤ Real.exp (-(k / (n : ℝ)) * N) := by
    have hbase : (0 : ℝ) ≤ 1 - k / (n : ℝ) := by
      have h1 : k / (n : ℝ) ≤ 1 := by
        rw [div_le_one hnr]
        exact hA_le_n
      linarith
    have hle : 1 - k / (n : ℝ) ≤ Real.exp (-(k / (n : ℝ))) := by
      have h := Real.add_one_le_exp (-(k / (n : ℝ)))
      linarith
    calc (1 - k / (n : ℝ)) ^ N ≤ (Real.exp (-(k / (n : ℝ)))) ^ N :=
          pow_le_pow_left₀ hbase hle N
      _ = Real.exp (-(k / (n : ℝ)) * N) := by
          rw [← Real.exp_nat_mul (-(k / (n : ℝ))) N]
          congr 1
          ring
  have hN_bound : 10 * ((n : ℝ) / k) * Real.logb 2 (n : ℝ) ≤ (N : ℝ) := by
    rw [hNdef]
    exact Nat.le_ceil _
  have hmul : 10 * Real.logb 2 (n : ℝ) ≤ (k / (n : ℝ)) * (N : ℝ) := by
    have hcoef : (0 : ℝ) < k / (n : ℝ) := div_pos hkpos hnr
    have h1 := mul_le_mul_of_nonneg_left hN_bound (le_of_lt hcoef)
    have h2 : (k / (n : ℝ)) * (10 * ((n : ℝ) / k) * Real.logb 2 (n : ℝ))
        = 10 * Real.logb 2 (n : ℝ) := by
      field_simp
    linarith
  have hstep4 : Real.exp (-(k / (n : ℝ)) * N) ≤ Real.exp (-(10 * Real.logb 2 (n : ℝ))) := by
    apply Real.exp_le_exp.mpr
    linarith
  -- convert the exponential bound to `n ^ (-10)`
  have hlog_eq : Real.exp (-(10 * Real.logb 2 (n : ℝ))) = (n : ℝ) ^ (-(10 / Real.log 2)) := by
    rw [Real.rpow_def_of_pos hnr]
    congr 1
    have hlogb : Real.logb 2 (n : ℝ) = Real.log (n : ℝ) / Real.log 2 := rfl
    rw [hlogb]
    field_simp
  have hlog_le : -(10 / Real.log 2) ≤ (-10 : ℝ) := by
    have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2le : Real.log 2 ≤ 1 := by
      have h := Real.log_two_lt_d9
      linarith
    rw [neg_le_neg_iff, le_div_iff₀ h2pos]
    nlinarith
  have hfinal : Real.exp (-(10 * Real.logb 2 (n : ℝ))) ≤ (n : ℝ) ^ (-10 : ℝ) := by
    rw [hlog_eq]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hlog_le
  have hkey : ((Finset.univ.filter (fun σ : Fin N → V => ∀ j, σ j ∉ A)).card : ℝ) /
        (n : ℝ) ^ N ≤ (n : ℝ) ^ (-10 : ℝ) := by
    rw [hratio]
    calc (((n : ℝ) - (A.card : ℝ)) / (n : ℝ)) ^ N
        ≤ (((n : ℝ) - k) / (n : ℝ)) ^ N := hstep1
      _ = (1 - k / (n : ℝ)) ^ N := hstep2
      _ ≤ Real.exp (-(k / (n : ℝ)) * N) := hstep3
      _ ≤ Real.exp (-(10 * Real.logb 2 (n : ℝ))) := hstep4
      _ ≤ (n : ℝ) ^ (-10 : ℝ) := hfinal
  have hgoal_eq : ((Finset.univ.filter (fun σ : Fin N → V => ∃ j, σ j ∈ A)).card : ℝ) /
        (Fintype.card (Fin N → V) : ℝ)
      = 1 - ((Finset.univ.filter (fun σ : Fin N → V => ∀ j, σ j ∉ A)).card : ℝ) / (n : ℝ) ^ N := by
    rw [htotal, hhit]
    have hpow : (n : ℝ) ^ N ≠ 0 := pow_ne_zero N hnne
    field_simp
  rw [hgoal_eq]
  linarith [hkey]
