-- Prove2me | solution 1 for LeanModelChecking.until_mpr.base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:48:34.281683+00:00
-- url     : https://prove2.me/submissions/2442cd11-a422-4e03-9fb2-916038e5a319

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_PositiveBool_sat_map_image
public import Theorems.Thm_LeanModelChecking_replaceRoot_runDag_accepting
public import Theorems.Thm_LeanModelChecking_and_mp_left
public import Theorems.Thm_LeanModelChecking_or_mpr_left

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
namespace until_mpr
theorem _root_.solution
  {S} {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
  (h2 : φ₂.toABW.language w)
    : (φ₁.until φ₂).toABW.language w := by
  classical
  simp only [ABW.language, NNF.toABW]
  obtain ⟨G, G_acc⟩ := h2
  exact ⟨replaceRoot.runDag (sub.until_right sub.refl) G
    (by
      simp only [delta, PositiveBool.mapSubtype, PositiveBool.Sat, Set.mem_image, Subtype.exists]
      intros
      left
      let : DecidablePred (· ∈ w 0) := by classical infer_instance
      rwa [←PositiveBool.sat_map_image (sub.until_right sub.refl) delta_forall])
    (by simp [NNF.toABW]),
    replaceRoot.runDag_accepting _ G_acc _ _ (by simp [NNF.toABW, Subtype.embedLe])⟩
end until_mpr
end LeanModelChecking
