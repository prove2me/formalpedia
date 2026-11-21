-- Prove2me | solution 1 for LeanModelChecking.or_mp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:48:33.744417+00:00
-- url     : https://prove2.me/submissions/f6de756e-901f-47d1-bf61-0901a814c92b

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
public import Theorems.Thm_LeanModelChecking_and_mp_right

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
theorem _root_.solution {S} {φ₁ φ₂ : NNF S} {w} : (φ₁.or φ₂).toABW.language w
    → φ₁.toABW.language w ∨ φ₂.toABW.language w := by
  simp only [ABW.language, NNF.toABW, forall_exists_index]
  intros G G_acc
  obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ G.p_root
  simp only [delta, PositiveBool.mapSubtype, PositiveBool.Sat] at p_sat
  rcases p_sat with p_sat|p_sat
  · left; apply subformula_toABW_lang (sub.or_left sub.refl) G_acc p_sat p_sub
  · right; apply subformula_toABW_lang (sub.or_right sub.refl) G_acc p_sat p_sub
end LeanModelChecking
