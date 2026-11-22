-- Prove2me | solution 1 for Lean4LPD.MultiLadder.sum_steps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:50.838175+00:00
-- url     : https://prove2.me/submissions/1c0683b4-385c-4f56-b919-fb73b5de48cb

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Assembly
public import Theorems.Thm_Lean4LPD_MultiLadder_majorant_eq_sum_range
public import Theorems.Thm_Lean4LPD_MultiLadder_le_majorant
public import Theorems.Thm_Lean4LPD_chain_nonneg
public import Theorems.Thm_Lean4LPD_sum_choose_mul_le


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.MultiLadder
open Finset
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ} {M : ℝ}
namespace Lean4LPD.MultiLadder
theorem _root_.solution (L : MultiLadder eps E M) (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m)
    (hM : 0 ≤ M) {G : ℕ} (hG : 1 ≤ G) {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    ∑ d ∈ range r, L.N m ((d + 1) * G)
      ≤ M * ∑ k ∈ range (m + 1),
          ((((r : ℝ) + 1) * G) ^ (k + 1) / ((G : ℝ) * (Nat.factorial (k + 1) : ℝ)))
            * chain eps E k m := by
  have hchain : ∀ k, 0 ≤ chain eps E k m := fun k => chain_nonneg heps hE k m
  -- step 1: the mass sampled at the end of each block is at most its majorant
  have h1 : ∑ d ∈ range r, L.N m ((d + 1) * G)
      ≤ ∑ d ∈ range r, M * ∑ k ∈ range (m + 1),
          ((((d + 1) * G).choose k : ℝ)) * chain eps E k m := by
    refine Finset.sum_le_sum fun d _ => ?_
    have := L.le_majorant heps ((d + 1) * G) m hm
    rwa [majorant_eq_sum_range hm ((d + 1) * G)] at this
  -- step 2: exchange the sums
  have h2 : ∑ d ∈ range r, M * ∑ k ∈ range (m + 1),
        ((((d + 1) * G).choose k : ℝ)) * chain eps E k m
      = M * ∑ k ∈ range (m + 1),
          (∑ d ∈ range r, (((d + 1) * G).choose k : ℝ)) * chain eps E k m := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
  -- step 3: the slot count, per k
  have h3 : ∑ k ∈ range (m + 1),
        (∑ d ∈ range r, (((d + 1) * G).choose k : ℝ)) * chain eps E k m
      ≤ ∑ k ∈ range (m + 1),
          ((((r : ℝ) + 1) * G) ^ (k + 1) / ((G : ℝ) * (Nat.factorial (k + 1) : ℝ)))
            * chain eps E k m := by
    refine Finset.sum_le_sum fun k _ => ?_
    exact mul_le_mul_of_nonneg_right (sum_choose_mul_le k r G hG) (hchain k)
  calc ∑ d ∈ range r, L.N m ((d + 1) * G)
      ≤ ∑ d ∈ range r, M * ∑ k ∈ range (m + 1),
          ((((d + 1) * G).choose k : ℝ)) * chain eps E k m := h1
    _ = M * ∑ k ∈ range (m + 1),
          (∑ d ∈ range r, (((d + 1) * G).choose k : ℝ)) * chain eps E k m := h2
    _ ≤ M * ∑ k ∈ range (m + 1),
          ((((r : ℝ) + 1) * G) ^ (k + 1) / ((G : ℝ) * (Nat.factorial (k + 1) : ℝ)))
            * chain eps E k m := mul_le_mul_of_nonneg_left h3 hM
end Lean4LPD.MultiLadder
