-- Prove2me | solution 1 for Lean4LPD.chain_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:25.494002+00:00
-- url     : https://prove2.me/submissions/61a66cef-7d06-4918-b78f-8d828e22b53e

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Theorems.Thm_Lean4LPD_chain_succ_succ
public import Theorems.Thm_Lean4LPD_chain_eq_zero_of_lt

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ}
namespace Lean4LPD
theorem _root_.solution :
    ∀ m : ℕ, 1 ≤ m → chain eps E m m = E 1 * ∏ i ∈ Ico 2 (m + 1), eps 1 i := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    match m with
    | 0 => simp
    | (m + 1) =>
      have hstep : chain eps E (m + 2) (m + 2)
          = ∑ j ∈ Ico 1 (m + 2), eps j (m + 2) * chain eps E (m + 1) (m + 2 - j) :=
        chain_succ_succ eps E m (m + 2)
      have honly : ∀ j ∈ Ico 1 (m + 2), j ≠ 1 →
          eps j (m + 2) * chain eps E (m + 1) (m + 2 - j) = 0 := by
        intro j hj hne
        rw [Finset.mem_Ico] at hj
        rw [chain_eq_zero_of_lt (m + 1) (m + 2 - j) (by omega) (by omega),
          mul_zero]
      rw [hstep, Finset.sum_eq_single 1 (fun j hj hne => honly j hj hne)
        (fun h => absurd (Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩) h)]
      have h1 : m + 2 - 1 = m + 1 := by omega
      rw [h1, ih (by omega)]
      have h2 : ∏ i ∈ Ico 2 (m + 3), eps 1 i = (∏ i ∈ Ico 2 (m + 2), eps 1 i) * eps 1 (m + 2) := by
        rw [Finset.prod_Ico_succ_top (by omega)]
      have h3 : m + 1 + 1 = m + 2 := rfl
      rw [h2, h3]; ring
end Lean4LPD
