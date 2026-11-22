-- Prove2me | solution 1 for Lean4LPD.diagFactor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:52.302551+00:00
-- url     : https://prove2.me/submissions/f285e24e-9593-4f4c-a1cc-ad31554c543a

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Theorems.Thm_Lean4LPD_diagFactor_ratio

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution (j : ℕ) (hj : 2 ≤ j) : diagFactor j ≤ (9 / 4 : ℝ) ^ (j - 1) := by
  induction j with
  | zero => omega
  | succ n ih =>
    match n, hj with
    | 1, _ =>
      norm_num [diagFactor, Nat.factorial]
    | (n + 2), _ =>
      have hn : 2 ≤ n + 2 := by omega
      have hstep := diagFactor_ratio (j := n + 2) hn
      have hih := ih hn
      have hpow : (9 / 4 : ℝ) ^ (n + 2 - 1) = (9 / 4 : ℝ) ^ (n + 1) := by norm_num
      have hgoal : (9 / 4 : ℝ) ^ (n + 2 + 1 - 1) = 9 / 4 * (9 / 4 : ℝ) ^ (n + 1) := by
        have : n + 2 + 1 - 1 = (n + 1) + 1 := by omega
        rw [this, pow_succ]; ring
      rw [hgoal]
      rw [hpow] at hih
      linarith [hstep, hih]
end Lean4LPD
