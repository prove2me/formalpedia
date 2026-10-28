-- Prove2me | solution 1 for MatrixAnalytic.Tree.matrix_product_form
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:54:08.193865+00:00
-- url     : https://prove2.me/submissions/f770935b-7e6c-4dbe-91ac-65556e93ea28

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_MatrixAnalytic_Tree_Model
import Theorems.Thm_MatrixAnalytic_Tree_node_step
import Theorems.Thm_MatrixAnalytic_Tree_marginal_stack_size

open scoped ENNReal

namespace S202MP
open MatrixAnalytic.Tree

lemma assoc {ι : Type*} (v : ι → ℝ≥0∞) (A M : ι → ι → ℝ≥0∞) (j : ι) :
    vecMulE v (matMulE A M) j = vecMulE (vecMulE v A) M j := by
  unfold vecMulE matMulE
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => tsum_congr fun i => ?_
  ring

end S202MP

open MatrixAnalytic.Tree in
theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T)
    (hpr : IsPositiveRecurrentProcess (gen T))
    (π : TreeState ι → ℝ) (hπ : IsStationaryCT (gen T) π) :
    ∀ (ns : List ι) (j : ι),
      ENNReal.ofReal (nodeVec π ns j) =
        (ns.foldl (fun v n => vecMulE v (matRi T n)) (vecMulE (rootVec T π) (matN T))) j := by
  have hroot : ∀ j, ENNReal.ofReal (nodeVec π [] j) = vecMulE (rootVec T π) (matN T) j := by
    intro j
    rw [← (MatrixAnalytic.Tree.marginal_stack_size T hT hpr π hπ).1 j]
    congr 1
    unfold stackMarginal nodeVec
    rw [tsum_eq_single []]
    · simp
    · intro l hl
      have : l.length + 1 ≠ 1 := by
        intro h; exact hl (List.length_eq_zero_iff.1 (by omega))
      simp [hl]
  intro ns
  induction ns using List.reverseRecOn with
  | nil => exact hroot
  | append_singleton l n ih =>
    intro j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil,
      MatrixAnalytic.Tree.node_step T hT hpr π hπ l n j, matRi, S202MP.assoc]
    rw [show (fun k => ENNReal.ofReal (nodeVec π l k)) =
      List.foldl (fun v n => vecMulE v (matRi T n)) (vecMulE (rootVec T π) (matN T)) l from funext ih]
