-- Prove2me | solution 1 for Lift.olift_evaluate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:01:07.383596+00:00
-- url     : https://prove2.me/submissions/5773f94a-bacb-4e14-9ee8-3a3be0cd46cb

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Lift
import Theorems.Thm_DecisionTree_lift_evaluate
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_P2M_OBdd_toTree_terminal__6f80b985dd51
attribute [local simp] Nary.restrict_const


section
set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered
namespace Lift
attribute [local implicit_reducible] olift
private lemma olift_low {h : n ≤ n'} {O : OBdd n m} {j : Fin m} (hr : O.1.root = .node j): (olift h O).low hr = olift h (O.low hr) := by
  simp only [OBdd.low, olift, lift]
  simp_rw [Bdd.low_heap_eq_heap]
  simp_rw [hr]
  simp [Bdd.low]
private lemma olift_high {h : n ≤ n'} {O : OBdd n m} {j : Fin m} (hr : O.1.root = .node j): (olift h O).high hr = olift h (O.high hr) := by
  simp only [OBdd.high, olift, lift]
  simp_rw [Bdd.high_heap_eq_heap]
  simp_rw [hr]
  simp [Bdd.high]
private lemma olift_preserves_toTree {h : n ≤ n'} {O : OBdd n m} : (olift h O).toTree = DecisionTree.lift h O.toTree := by
  cases O_root_def : O.1.root with
  | terminal b =>
    simp only [OBdd.toTree_terminal' O_root_def, DecisionTree.lift, olift, lift]
    simp_rw [O_root_def, OBdd.toTree_terminal]
  | node j =>
    simp only [OBdd.toTree_node O_root_def, DecisionTree.lift]
    rw [← olift_preserves_toTree (h := h) (O := (O.low  O_root_def))]
    rw [← olift_preserves_toTree (h := h) (O := (O.high O_root_def))]
    rw [← olift_preserves_root (h := h)] at O_root_def
    simp only [OBdd.toTree_node O_root_def]
    simp only [DecisionTree.branch.injEq]
    constructor
    · simp [olift]
    · constructor
      · exact congrArg OBdd.toTree (olift_low (h := h) (O := O) (j := j) (by simpa [olift] using O_root_def))
      · exact congrArg OBdd.toTree (olift_high (h := h) (O := O) (j := j) (by simpa [olift] using O_root_def))
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
end Lift
end

set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered
open Lift
attribute [local implicit_reducible] olift
namespace Lift
theorem _root_.solution {h : n ≤ n'} {O : OBdd n m} {I : Vector Bool n'} :
    (olift h O).evaluate I = O.evaluate (Vector.cast (by simpa) (I.take n)) := by
  simp only [OBdd.evaluate, Function.comp_apply, olift_preserves_toTree]
  rw [DecisionTree.lift_evaluate]
end Lift
