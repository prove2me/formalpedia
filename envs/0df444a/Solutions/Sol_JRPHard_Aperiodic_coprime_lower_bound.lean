-- Prove2me | solution 1 for JRPHard.Aperiodic.coprime_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T10:48:35.788587+00:00
-- url     : https://prove2.me/submissions/e55e88c2-6c0a-4bed-b9e2-50fab81cf56d

import Definitions.Def_JRPHard_Aperiodic_Setting
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open JRPHard.Aperiodic

theorem solution (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime)
    (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime q M) :
    jrpRed M q = ((M : ℝ) - 1) ^ 2 / (q : ℝ) + 4 * (q : ℝ) ∧
      4 * ((M : ℝ) - 1) ≤ jrpRed M q := by
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have heq : jrpRed M q = ((M : ℝ) - 1) ^ 2 / q + 4 * q := by
    unfold jrpRed
    rw [hcop.lcm_eq_mul, Nat.cast_mul]
    field_simp
    <;> ring
  refine ⟨heq, ?_⟩
  rw [heq]
  have hs : (4 * ((M : ℝ) - 1) - 4 * q) * q ≤ ((M : ℝ) - 1) ^ 2 := by
    nlinarith [sq_nonneg ((M : ℝ) - 1 - 2 * q)]
  have hd := (le_div_iff₀ hqR).mpr hs
  linarith
