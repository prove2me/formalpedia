-- Prove2me | solution 1 for LeanModelChecking.PositiveBool.mapSubtype_contract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:06.62318+00:00
-- url     : https://prove2.me/submissions/204bdb7d-163c-4842-bcb5-ac1d60bbcca0

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.PositiveBool
namespace LeanModelChecking.PositiveBool
theorem _root_.solution
  {α} {P Q : α → Prop}
  {φ : PositiveBool α}
  {Y : Set (Subtype P)} {fq : φ.Forall Q} {fp : φ.Forall P}
  (hsat : (φ.mapSubtype fp).Sat Y) (f : Subtype P → Subtype Q)
  (hf : ∀ (x : Subtype P), Q (x.val) → (f x).val = x)
    : (φ.mapSubtype fq).Sat (f '' Y) := by
  induction φ <;> simp [mapSubtype, Sat] at hsat ⊢ <;> simp [Forall] at fp fq <;> grind
end LeanModelChecking.PositiveBool
