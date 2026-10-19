-- Prove2me | solution 1 for JRPHard.Aperiodic.exists_good_multiple
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T10:35:42.37331+00:00
-- url     : https://prove2.me/submissions/2331d351-c9ca-420e-8b4d-9235908fe396

import Definitions.Def_JRPHard_Aperiodic_Setting
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open JRPHard.Aperiodic

private lemma multiple_bound (M p q : ℕ) (h1 : 1 < M) (hpM : p ∣ M)
    (hq : 0 < q) (hpq : p ∣ q) :
    (p : ℝ) * ((M : ℝ) - 1) / (q : ℝ) ≤ (coefK0 M : ℝ) / (Nat.lcm q M : ℝ) ∧
      jrpRed M q ≤ ((M : ℝ) - 1) * ((M : ℝ) - p) / (q : ℝ) + 4 * (q : ℝ) := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hl : 0 < (Nat.lcm q M : ℝ) := by
    exact_mod_cast Nat.lcm_pos hq (show 0 < M by omega)
  have hpG : p ≤ Nat.gcd q M :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_left M hq) (Nat.dvd_gcd hpq hpM)
  have hpGR : (p : ℝ) ≤ (Nat.gcd q M : ℝ) := by exact_mod_cast hpG
  have hsub : 0 ≤ (M : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ M by omega))
  have hprod : (Nat.gcd q M : ℝ) * (Nat.lcm q M : ℝ) = (q : ℝ) * M := by
    exact_mod_cast Nat.gcd_mul_lcm q M
  have hcoef : (coefK0 M : ℝ) = (M : ℝ) * ((M : ℝ) - 1) := by
    simp [coefK0, Nat.cast_sub (show 1 ≤ M by omega)]
  have hdiscount : (p : ℝ) * ((M : ℝ) - 1) / q ≤
      (coefK0 M : ℝ) / (Nat.lcm q M : ℝ) := by
    rw [hcoef]
    apply (div_le_div_iff₀ hqR hl).mpr
    calc
      (p : ℝ) * ((M : ℝ) - 1) * (Nat.lcm q M : ℝ) ≤
          (Nat.gcd q M : ℝ) * ((M : ℝ) - 1) * (Nat.lcm q M : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpGR hsub) hl.le
      _ = (M : ℝ) * ((M : ℝ) - 1) * q := by
        calc
          _ = ((Nat.gcd q M : ℝ) * (Nat.lcm q M : ℝ)) * ((M : ℝ) - 1) := by ring
          _ = _ := by rw [hprod]; ring
  refine ⟨hdiscount, ?_⟩
  calc
    jrpRed M q = (M : ℝ) * ((M : ℝ) - 1) / q + 4 * q -
        (coefK0 M : ℝ) / (Nat.lcm q M : ℝ) := by rw [hcoef]; unfold jrpRed; ring
    _ ≤ (M : ℝ) * ((M : ℝ) - 1) / q + 4 * q -
        (p : ℝ) * ((M : ℝ) - 1) / q := sub_le_sub_left hdiscount _
    _ = ((M : ℝ) - 1) * ((M : ℝ) - p) / q + 4 * q := by ring

theorem solution (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime)
    (p : ℕ) (hpM : p ∣ M) (hp3 : 3 ≤ p) (hplt : p < M) :
    ∃ q : ℕ, 0 < q ∧ p ∣ q ∧
      (M - 1) / 2 - (p - 1) / 2 ≤ q ∧ q ≤ (M - 1) / 2 + (p - 1) / 2 ∧
      jrpRed M q < 4 * ((M : ℝ) - 1) := by
  obtain ⟨r, hr⟩ := hpM
  have hpr : Odd (p * r) := hr ▸ hodd
  obtain ⟨a, ha⟩ := (Nat.odd_mul.mp hpr).1
  obtain ⟨b, hb⟩ := (Nat.odd_mul.mp hpr).2
  let q := p * b
  have hMq : M = 2 * q + p := by rw [hr, hb]; dsimp [q]; ring
  have hq : 0 < q := by omega
  have hpq : p ∣ q := ⟨b, rfl⟩
  have hphalf : (p - 1) / 2 = a := by omega
  have hMhalf : (M - 1) / 2 = q + a := by omega
  refine ⟨q, hq, hpq, ?_, ?_, ?_⟩
  · rw [hMhalf, hphalf]
    omega
  · rw [hMhalf, hphalf]
    omega
  · have hupper := (multiple_bound M p q h1 ⟨r, hr⟩ hq hpq).2
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hMqR : (M : ℝ) = 2 * q + p := by exact_mod_cast hMq
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hdiff : (M : ℝ) - p = 2 * q := by linarith
    rw [hdiff] at hupper
    have hsimp : ((M : ℝ) - 1) * (2 * q) / q + 4 * q =
        2 * ((M : ℝ) - 1) + 4 * q := by field_simp
    rw [hsimp] at hupper
    linarith

