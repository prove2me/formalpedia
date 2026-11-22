-- Prove2me | solution 1 for Lean4LPD.MultiLadder.sum_block_inflow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:08:51.757919+00:00
-- url     : https://prove2.me/submissions/9bac409b-0f10-4d51-ac15-25e1ea04eb64

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Theorems.Thm_Lean4LPD_MultiLadder_sum_inflow_majorant_le
public import Theorems.Thm_Lean4LPD_MultiLadder_block_inflow_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.MultiLadder
open Finset
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ} {M : ℝ}
namespace Lean4LPD.MultiLadder
theorem _root_.solution (L : MultiLadder eps E M) (heps : ∀ j m, 0 ≤ eps j m)
    (hE : ∀ m, 0 ≤ E m) (hM : 0 ≤ M) {m G : ℕ} (hm : 1 ≤ m) (hG : 1 ≤ G)
    (r : ℕ) (x : ℕ → ℕ → ℝ)
    (hreset : ∀ d, d < r → x d 0 = 0)
    (hinflow : ∀ d, d < r → ∀ i, i < G → x d (i + 1) ≤ x d i +
      (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) (d * G + i)) + E m * M) :
    (∑ d ∈ range r, x d G) ≤ M * ∑ k ∈ range m,
      ((((r : ℝ) + 1) * G) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) *
        chain eps E (k + 1) m := by
  refine le_trans ?_ (sum_inflow_majorant_le heps hE hM hG hm r)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  have hd' := Finset.mem_range.mp hd
  have h := block_inflow_le L heps hE hM (x d) (hreset d hd') (hinflow d hd')
  simpa only [Nat.add_mul, Nat.one_mul] using h
end Lean4LPD.MultiLadder
