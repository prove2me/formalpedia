-- Prove2me | solution 1 for LeanModelChecking.release_mp.right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:48:34.761582+00:00
-- url     : https://prove2.me/submissions/7e3054b1-4e29-4743-abbc-f05796059797

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_subformula_toABW_lang
public import Theorems.Thm_LeanModelChecking_and_mp_left
public import Theorems.Thm_LeanModelChecking_or_mpr_left

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.release_mp
variable {S} {φ₁ φ₂ : NNF S} {w : ℕ → Letter S} {G : RunDAG (φ₁.release φ₂).toABW w}
namespace LeanModelChecking.release_mp
theorem _root_.solution (G_acc : G.accepting) {l} (H : (⟨φ₁.release φ₂, le_refl _⟩,
    l) ∈ G.V) : φ₂.toABW.language (fun j => w (j + l)) := by
  obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ H
  apply subformula_toABW_lang (sub.release_right sub.refl) G_acc p_sat.left p_sub
end LeanModelChecking.release_mp
