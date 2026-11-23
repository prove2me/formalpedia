-- Prove2me | solution 1 for Lift.olift_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:09:07.348898+00:00
-- url     : https://prove2.me/submissions/ab061be2-bf21-4972-8009-b89772d5a5f1

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Lift
import Theorems.Thm_Lift_olift_evaluate
import Theorems.Thm_DecisionTree_lift_injective
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_P2M_OBdd_toTree_terminal__6f80b985dd51
attribute [local simp] Nary.restrict_const


attribute [local simp] Lift.olift_evaluate
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
private lemma NoRedundancy_of_olift {h : n ≤ n'} {O : OBdd n m} : O.1.NoRedundancy → (olift h O).1.NoRedundancy := by
  rintro hnr ⟨p, hp⟩ contra
  simp only at contra
  cases p_def : p with
  | terminal _ =>
    cases contra with
    | red _ => contradiction
  | node j =>
    rw [p_def] at contra
    cases contra with
    | red red =>
      simp only [olift, lift, Fin.getElem_fin] at red
      apply hnr ⟨p, (lift_reachable_iff (h := h)).mpr hp⟩
      simp_rw [p_def]
      constructor
      simp_all
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
private lemma olift_SimilarRP {h : n ≤ n'} {O : OBdd n m} {p q : Pointer m}
    {hp : Pointer.Reachable (olift h O).1.heap (olift h O).1.root p}
    {hq : Pointer.Reachable (olift h O).1.heap (olift h O).1.root q} :
    (olift h O).SimilarRP ⟨p, hp⟩ ⟨q, hq⟩ →
    O.SimilarRP ⟨p, (lift_reachable_iff (h := h)).mpr hp⟩ ⟨q, (lift_reachable_iff (h := h)).mpr hq⟩ := by
  intro sim
  simp only [OBdd.SimilarRP, OBdd.Similar, OBdd.HSimilar] at sim
  have : OBdd.toTree ⟨{heap := (olift h O).1.heap, root := p}, Bdd.ordered_of_reachable hp⟩ = OBdd.toTree (olift h ⟨{heap := O.1.heap, root := p}, Bdd.ordered_of_reachable ((lift_reachable_iff (h := h)).mpr hp)⟩) := by
    rfl
  rw [this] at sim
  have : OBdd.toTree ⟨{heap := (olift h O).1.heap, root := q}, Bdd.ordered_of_reachable hq⟩ = OBdd.toTree (olift h ⟨{heap := O.1.heap, root := q}, Bdd.ordered_of_reachable ((lift_reachable_iff (h := h)).mpr hq)⟩) := by
    rfl
  rw [this] at sim
  rw [olift_preserves_toTree] at sim
  rw [olift_preserves_toTree] at sim
  clear this
  clear this
  simp only [OBdd.SimilarRP, OBdd.Similar,OBdd.HSimilar]
  rw [DecisionTree.lift_injective sim]
end Lift
end

set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered
open Lift
attribute [local implicit_reducible] olift
namespace Lift
theorem _root_.solution {h : n ≤ n'} {O : OBdd n m} : O.Reduced → (olift h O).Reduced := by
  rintro ⟨r1, r2⟩
  constructor
  · exact NoRedundancy_of_olift r1
  · rintro _ _ sim; exact r2 (olift_SimilarRP sim)
end Lift
