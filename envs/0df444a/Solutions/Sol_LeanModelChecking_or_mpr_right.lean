-- Prove2me | solution 1 for LeanModelChecking.or_mpr.right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:21.66296+00:00
-- url     : https://prove2.me/submissions/34045ac6-043a-4386-bb6d-15a04cf453b7

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
theorem _root_.solution : φ₂.toABW.language w → (φ₁.or φ₂).toABW.language w := by
  classical
  rintro ⟨G, G_acc⟩
  exact ⟨replaceRoot.runDag (sub.or_right sub.refl) G
    (by
      simp only [NNF.toABW, delta, PositiveBool.mapSubtype, PositiveBool.Sat]
      intros
      apply Or.inr
      let : DecidablePred (· ∈ w 0) := by classical infer_instance
      rwa [←PositiveBool.sat_map_image (sub.or_right sub.refl) delta_forall])
    (by simp [NNF.toABW]),
    replaceRoot.runDag_accepting _ G_acc _ _ (by simp [NNF.toABW, Subtype.embedLe])⟩
end LeanModelChecking.or_mpr
