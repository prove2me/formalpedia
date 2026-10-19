-- Prove2me | solution 1 for JRPHard.Aperiodic.item2_pinned
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T10:52:55.844111+00:00
-- url     : https://prove2.me/submissions/d04b4002-5709-4d58-8f81-44b486611847

import Definitions.Def_JRPHard_Aperiodic_Setting
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

import Theorems.Thm_JRPHard_Aperiodic_eoq_shift

open JRPHard.Aperiodic


private lemma cost_ge_item2 (M a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    4 * (a : ℝ) + eoq2 M b ≤ lemma1Cost M a b := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hden : (a : ℝ) ≤ (Nat.lcm a b : ℝ) := by exact_mod_cast Nat.le_lcm_left a hb
  have hdisc : (coefK0 M : ℝ) / (Nat.lcm a b : ℝ) ≤ (coefK0 M : ℝ) / a :=
    div_le_div_of_nonneg_left (by positivity) haR hden
  have hform : lemma1Cost M a b = (coefK0 M : ℝ) / a + 4 * a + eoq2 M b -
      (coefK0 M : ℝ) / (Nat.lcm a b : ℝ) := by rfl
  rw [hform]
  linarith

private lemma eoq_away (M b : ℕ) (hM : 2 ≤ M) (hb : 0 < b) (hne : b ≠ M) :
    eoq2 M (M + 1) ≤ eoq2 M b := by
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hplus : 0 < (M : ℝ) + 1 := by linarith
  have hprod : 0 ≤ ((b : ℝ) - ((M : ℝ) + 1)) *
      ((b : ℝ) * ((M : ℝ) + 1) - (M : ℝ) ^ 2) := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hle : (b : ℝ) + 1 ≤ M := by exact_mod_cast Nat.succ_le_of_lt h
      have hbound := mul_le_mul_of_nonneg_right (show (b : ℝ) ≤ (M : ℝ) - 1 by linarith) hplus.le
      apply mul_nonneg_of_nonpos_of_nonpos <;> nlinarith
    · have hle : (M : ℝ) + 1 ≤ b := by exact_mod_cast Nat.succ_le_of_lt h
      have hbound := mul_le_mul_of_nonneg_right hle hplus.le
      apply mul_nonneg <;> nlinarith
  have hid : (M : ℝ) ^ 2 / b + b - ((M : ℝ) ^ 2 / ((M : ℝ) + 1) + ((M : ℝ) + 1)) =
      (((b : ℝ) - ((M : ℝ) + 1)) * ((b : ℝ) * ((M : ℝ) + 1) - (M : ℝ) ^ 2)) /
        ((b : ℝ) * ((M : ℝ) + 1)) := by
    field_simp
    <;> ring
  have hbase : (M : ℝ) ^ 2 / ((M : ℝ) + 1) + ((M : ℝ) + 1) ≤ (M : ℝ) ^ 2 / b + b := by
    have hd := div_nonneg hprod (mul_nonneg hbR.le hplus.le)
    rw [← hid] at hd
    linarith
  have heoq (q : ℕ) : eoq2 M q = (coefH2 M : ℝ) * ((M : ℝ) ^ 2 / q + q) := by
    simp [eoq2, eoq, coefK2, coefH2]
    <;> ring
  rw [heoq, heoq]
  push_cast
  exact mul_le_mul_of_nonneg_left hbase (by positivity)

theorem solution (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime) :
    (∀ q₁ q₂ : ℕ, 0 < q₁ → 0 < q₂ → q₂ ≠ M →
      4 * (q₁ : ℝ) + min (eoq2 M (M - 1)) (eoq2 M (M + 1)) ≤ lemma1Cost M q₁ q₂ ∧
      eoq2 M M + (coefK0 M : ℝ) + 4 ≤ lemma1Cost M q₁ q₂) ∧
    lemma1Cost M 1 M < eoq2 M M + (coefK0 M : ℝ) + 4 := by
  have hM : 2 ≤ M := by omega
  have hshift := JRPHard.Aperiodic.eoq_shift M hM
  constructor
  · intro a b ha hb hne
    have hcost := cost_ge_item2 M a b ha hb
    have haway := eoq_away M b hM hb hne
    have hshiftK : eoq2 M M + (coefK0 M : ℝ) ≤ eoq2 M (M + 1) := by
      rw [hshift.1.1]
      linarith [hshift.1.2]
    constructor
    · linarith [min_le_right (eoq2 M (M - 1)) (eoq2 M (M + 1))]
    · have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
      linarith
  · have hMR : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
    have hK : 0 < (coefK0 M : ℝ) := by
      exact_mod_cast Nat.mul_pos (show 0 < M by omega) (show 0 < M - 1 by omega)
    have hform : lemma1Cost M 1 M = eoq2 M M + (coefK0 M : ℝ) + 4 - (coefK0 M : ℝ) / M := by
      simp [lemma1Cost, aperiodicCost, eoq2, eoq, coefK0, coefK1, coefH1]
      <;> ring
    rw [hform]
    exact sub_lt_self _ (div_pos hK hMR)

