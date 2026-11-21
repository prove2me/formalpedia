-- Prove2me | solution 1 for LeanModelChecking.and_mp.right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:47:58.17597+00:00
-- url     : https://prove2.me/submissions/b14152e0-9b97-4706-b2ad-b1890dd54289

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
theorem _root_.solution {S} {φ₁ φ₂ : NNF S} {w} : (φ₁.and φ₂).toABW.language w
    → φ₂.toABW.language w := by
  simp only [ABW.language, forall_exists_index]
  intros G G_acc
  obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ G.p_root
  apply subformula_toABW_lang (sub.and_right sub.refl) G_acc p_sat.right p_sub
end and_mp
end LeanModelChecking
