-- Prove2me | solution 1 for Lean4LPD.MultiLadder.block_inflow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:54.93575+00:00
-- url     : https://prove2.me/submissions/aa3eff17-9af8-4eef-845f-0a8e2f9b6728

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Theorems.Thm_Lean4LPD_MultiLadder_le_majorant
public import Theorems.Thm_Lean4LPD_MultiLadder_majorant_mono


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.MultiLadder
open Finset
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ} {M : ℝ}
namespace Lean4LPD.MultiLadder
theorem _root_.solution (L : MultiLadder eps E M) (heps : ∀ j m, 0 ≤ eps j m)
    (hE : ∀ m, 0 ≤ E m) (hM : 0 ≤ M) {m T G : ℕ}
    (x : ℕ → ℝ) (hreset : x 0 = 0)
    (hinflow : ∀ i, i < G → x (i + 1) ≤ x i +
      (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) (T + i)) + E m * M) :
    x G ≤ (G : ℝ) *
      ((∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) (T + G)) + E m * M) := by
  let C := (∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) (T + G)) + E m * M
  have hbound : ∀ i, i ≤ G → x i ≤ (i : ℝ) * C := by
    intro i
    induction i with
    | zero => intro _; simp [hreset]
    | succ i ih =>
      intro hi
      have hi' : i ≤ G := by omega
      have hsum : (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) (T + i)) ≤
          ∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) (T + G) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' := Finset.mem_Ico.mp hj
        apply mul_le_mul_of_nonneg_left _ (heps j m)
        refine le_trans (L.le_majorant heps (T + i) (m - j) (by omega)) ?_
        exact (monotone_nat_of_le_succ
          (majorant_mono heps hE hM (m - j))) (Nat.add_le_add_left hi' T)
      calc
        x (i + 1) ≤ x i + (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) (T + i)) + E m * M :=
          hinflow i (by omega)
        _ ≤ (i : ℝ) * C +
            (∑ j ∈ Ico 1 m, eps j m * majorant eps E M (m - j) (T + G)) + E m * M :=
          add_le_add (add_le_add (ih hi') hsum) le_rfl
        _ = ((i + 1 : ℕ) : ℝ) * C := by dsimp [C]; push_cast; ring
  exact hbound G le_rfl
end Lean4LPD.MultiLadder
