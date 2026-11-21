-- Prove2me | solution 1 for LeanModelChecking.or_mpr.left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:21.033065+00:00
-- url     : https://prove2.me/submissions/563849b4-3d80-4d82-a670-bba4e56f4c47

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

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.or_mpr
variable {S} [DecidableEq S] {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
omit [DecidableEq S]
namespace LeanModelChecking.or_mpr
theorem _root_.solution : φ₁.toABW.language w → (φ₁.or φ₂).toABW.language w := by
  classical
  rintro ⟨G, G_acc⟩
  exact ⟨replaceRoot.runDag (sub.or_left sub.refl) G
    (by
      simp only [NNF.toABW, delta, PositiveBool.mapSubtype, PositiveBool.Sat]
      intros
      apply Or.inl
      let : DecidablePred (· ∈ w 0) := by classical infer_instance
      rwa [←PositiveBool.sat_map_image (sub.or_left sub.refl) delta_forall])
    (by simp [NNF.toABW]),
    replaceRoot.runDag_accepting _ G_acc _ _ (by simp [NNF.toABW, Subtype.embedLe])⟩
end LeanModelChecking.or_mpr
