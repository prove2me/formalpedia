-- Prove2me | solution 1 for Lean4LPD.MultiLadder.majorant_inflow_eq_shifted_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:39.748927+00:00
-- url     : https://prove2.me/submissions/3f20d5f8-0bad-41e1-b0af-e4929b8a07f9

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Theorems.Thm_Lean4LPD_MultiLadder_sum_chain_shift


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.MultiLadder
open Finset
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ} {M : ℝ}
namespace Lean4LPD.MultiLadder
theorem _root_.solution (m T : ℕ) :
    (∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) T) + E m * M =
      M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E (k + 1) m := by
  have hsum : (∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) T) =
      M * ∑ j ∈ Ico 1 m, eps j m *
        ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold majorant
    ring
  rw [hsum, sum_chain_shift]
  ring
end Lean4LPD.MultiLadder
