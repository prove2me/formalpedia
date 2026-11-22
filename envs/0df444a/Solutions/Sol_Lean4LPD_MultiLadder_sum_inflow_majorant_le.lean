-- Prove2me | solution 1 for Lean4LPD.MultiLadder.sum_inflow_majorant_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:08:00.169502+00:00
-- url     : https://prove2.me/submissions/3d175970-b776-482a-89f2-eeadc4839c39

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Theorems.Thm_Lean4LPD_MultiLadder_majorant_inflow_eq_shifted_chain
public import Theorems.Thm_Lean4LPD_MultiLadder_shifted_chain_sum_eq_range
public import Theorems.Thm_Lean4LPD_chain_nonneg
public import Theorems.Thm_Lean4LPD_sum_choose_mul_le


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.MultiLadder
open Finset
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ} {M : ℝ}
namespace Lean4LPD.MultiLadder
theorem _root_.solution (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m)
    (hM : 0 ≤ M) {G m : ℕ} (hG : 1 ≤ G) (hm : 1 ≤ m) (r : ℕ) :
    (G : ℝ) * ∑ d ∈ range r,
      ((∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) ((d + 1) * G)) + E m * M) ≤
      M * ∑ k ∈ range m,
        ((((r : ℝ) + 1) * G) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) *
          chain eps E (k + 1) m := by
  have hGpos : (0 : ℝ) < G := by exact_mod_cast hG
  have hslots (k : ℕ) : (G : ℝ) *
      (∑ d ∈ range r, (((d + 1) * G).choose k : ℝ)) ≤
      (((r : ℝ) + 1) * G) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
    calc
      (G : ℝ) * (∑ d ∈ range r, (((d + 1) * G).choose k : ℝ)) ≤
          G * ((((r : ℝ) + 1) * G) ^ (k + 1) /
            ((G : ℝ) * (Nat.factorial (k + 1) : ℝ))) :=
        mul_le_mul_of_nonneg_left (sum_choose_mul_le k r G hG) hGpos.le
      _ = (((r : ℝ) + 1) * G) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
        field_simp
  have hswap : (G : ℝ) * ∑ d ∈ range r,
      M * ∑ k ∈ range m, (((d + 1) * G).choose k : ℝ) * chain eps E (k + 1) m =
      M * ∑ k ∈ range m,
        ((G : ℝ) * ∑ d ∈ range r, (((d + 1) * G).choose k : ℝ)) *
          chain eps E (k + 1) m := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  simp_rw [majorant_inflow_eq_shifted_chain, shifted_chain_sum_eq_range hm]
  rw [hswap]
  apply mul_le_mul_of_nonneg_left _ hM
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_right (hslots k) (chain_nonneg heps hE (k + 1) m)
end Lean4LPD.MultiLadder
