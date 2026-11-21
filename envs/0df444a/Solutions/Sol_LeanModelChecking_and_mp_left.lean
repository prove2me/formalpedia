-- Prove2me | solution 1 for LeanModelChecking.and_mp.left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:47:57.648026+00:00
-- url     : https://prove2.me/submissions/b8c4f896-fb89-492b-be2a-c7a6bc9c1e6a

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_subformula_toABW_lang

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
namespace and_mp
theorem _root_.solution {S} {φ₁ φ₂ : NNF S} {w} : (φ₁.and φ₂).toABW.language w → φ₁.toABW.language w := by
  simp only [ABW.language, forall_exists_index]
  intros G G_acc
  obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ G.p_root
  apply subformula_toABW_lang (sub.and_left sub.refl) G_acc p_sat.left p_sub
end and_mp
end LeanModelChecking
