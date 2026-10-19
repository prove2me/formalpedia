-- Prove2me | solution 1 for JRPHard.Aperiodic.multiple_of_M
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T10:48:39.68184+00:00
-- url     : https://prove2.me/submissions/f6b84cea-4e05-430d-9431-12a357a9fbb3

import Definitions.Def_JRPHard_Aperiodic_Setting
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open JRPHard.Aperiodic

theorem solution (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime) :
    (∀ q : ℕ, 0 < q → M ∣ q → jrpRed M q = 4 * (q : ℝ) ∧ 4 * (M : ℝ) ≤ jrpRed M q) ∧
      jrpRed M ((M - 1) / 2) ≤ 4 * ((M : ℝ) - 1) := by
  constructor
  · intro q hq hMq
    have heq : jrpRed M q = 4 * (q : ℝ) := by
      simp [jrpRed, Nat.lcm_eq_left hMq]
    refine ⟨heq, ?_⟩
    rw [heq]
    exact_mod_cast Nat.mul_le_mul_left 4 (Nat.le_of_dvd hq hMq)
  · obtain ⟨a, ha⟩ := hodd
    have hMa : M = 1 + 2 * a := by omega
    have hapos : 0 < a := by omega
    have hhalf : (M - 1) / 2 = a := by omega
    have hcop : Nat.Coprime a M := by
      rw [hMa, Nat.coprime_add_mul_right_right]
      exact Nat.coprime_one_right a
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast hapos.ne'
    have hMR : (M : ℝ) = 1 + 2 * a := by exact_mod_cast hMa
    rw [hhalf]
    unfold jrpRed
    rw [hcop.lcm_eq_mul, Nat.cast_mul, hMR]
    field_simp
    <;> nlinarith
