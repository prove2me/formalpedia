-- Prove2me | solution 1 for LeanModelChecking.next_mpr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:47:21.631117+00:00
-- url     : https://prove2.me/submissions/3f972252-4e09-4316-86bd-e76f052ac11c

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_replaceRoot_preserves_path
public import Theorems.Thm_LeanModelChecking_shiftDag_preserves_path
public import Theorems.Thm_LeanModelChecking_conjoinDag_preserves_path
public import Theorems.Thm_LeanModelChecking_filterDag_preserves_path
public import Theorems.Thm_LeanModelChecking_alwaysDag_preserves_path

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
theorem _root_.solution {AP : Type} {φ : NNF AP} {w} : (φ.toABW.language fun j =>
    w (j + 1)) → φ.next.toABW.language w := by
  rintro ⟨G, G_acc⟩
  have : DecidableEq AP := by classical infer_instance
  exists shiftDag.runDag (sub.next sub.refl) G
    (by simp [NNF.toABW, delta, PositiveBool.mapSubtype, PositiveBool.Sat])
    (by simp [NNF.toABW])
  simp only [RunDAG.accepting, NNF.toABW, ge_iff_le, Set.mem_ofPred_eq, shiftDag.runDag] at G_acc ⊢
  intros p p_path i
  have p_path := shiftDag.preserves_path _ _ _ _ _ _ p_path
  specialize G_acc _ p_path i
  obtain ⟨j, G_acc⟩ := G_acc
  exists (j + 1)
  grind
end LeanModelChecking
