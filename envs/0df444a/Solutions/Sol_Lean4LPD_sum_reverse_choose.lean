-- Prove2me | solution 1 for Lean4LPD.sum_reverse_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:32.658357+00:00
-- url     : https://prove2.me/submissions/cb00c2ce-195b-4675-b7af-063e0f1fabaa

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Theorems.Thm_Lean4LPD_sum_range_choose_real


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    (∑ j ∈ Ico 1 m, ((m - j - 1).choose k : ℝ)) = ((m - 1).choose (k + 1) : ℝ) := by
  simp_rw [show ∀ j : ℕ, m - j - 1 = (m - 1) - j from fun j => by omega]
  rw [Finset.sum_Ico_reflect (fun j => (j.choose k : ℝ)) 1 (by omega)]
  rw [Nat.sub_add_cancel hm, Nat.sub_self, Nat.Ico_zero_eq_range, sum_range_choose_real]
end Lean4LPD
