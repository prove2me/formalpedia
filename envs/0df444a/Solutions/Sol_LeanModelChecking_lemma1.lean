-- Prove2me | solution 1 for LeanModelChecking.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:18.186465+00:00
-- url     : https://prove2.me/submissions/f76015da-4bf5-43d6-bf5e-e4e5a9c6cc6b

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Order.KonigLemma
public import Definitions.Def_LeanPool_LeanModelChecking_ABWNBW

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
theorem _root_.solution {α : Type} {a b c : Set α} {h : Disjoint a b} : a = (a ∪ (b ∩ c)) \ b := by
  rw [Set.union_sdiff_distrib, Disjoint.sdiff_eq_right h.symm, ← Set.sdiff_inter_right_comm]
  simp
end LeanModelChecking
