-- Prove2me | solution 1 for LocalLemma.exp_regular_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:40.833119+00:00
-- url     : https://prove2.me/submissions/559c16ea-336e-444c-bf24-786a78247572

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution (k : ℕ) (hk : 9 ≤ k) :
    Real.exp 1 * (((k * (k - 1) : ℕ) : ℝ) + 1) ≤ 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num; linarith [Real.exp_one_lt_d9]
  | succ m hm ih =>
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hj : (8:ℝ) ≤ j := by exact_mod_cast (by omega : 8 ≤ j)
    have hstep : (((j + 1 + 1) * (j + 1 + 1 - 1) : ℕ) : ℝ) + 1 ≤
        2 * ((((j + 1) * (j + 1 - 1) : ℕ) : ℝ) + 1) := by
      simp only [Nat.add_sub_cancel]
      push_cast
      nlinarith
    have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    calc Real.exp 1 * ((((j + 1 + 1) * (j + 1 + 1 - 1) : ℕ) : ℝ) + 1)
        ≤ Real.exp 1 * (2 * ((((j + 1) * (j + 1 - 1) : ℕ) : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hstep he
      _ = 2 * (Real.exp 1 * ((((j + 1) * (j + 1 - 1) : ℕ) : ℝ) + 1)) := by ring
      _ ≤ 2 * 2 ^ (j + 1 - 1) := by linarith
      _ = 2 ^ (j + 1 + 1 - 1) := by simp [pow_succ]; ring
end LocalLemma
