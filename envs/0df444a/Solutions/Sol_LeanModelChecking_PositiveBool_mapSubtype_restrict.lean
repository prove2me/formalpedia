-- Prove2me | solution 1 for LeanModelChecking.PositiveBool.mapSubtype_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:09.820542+00:00
-- url     : https://prove2.me/submissions/07ddff82-18f1-418c-af02-d19ad7563c71

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
theorem _root_.solution {T : Type} {α β : T → Prop} {ψ : PositiveBool T} {Y : Set (Subtype α)}
  (all_α : ψ.Forall α) (all_β : ψ.Forall β) (hle : ∀ {q}, β q → α q)
  (p_sat : PositiveBool.Sat Y (ψ.mapSubtype all_α))
    : PositiveBool.Sat {q | ⟨q.val, hle q.prop⟩ ∈ Y} (ψ.mapSubtype all_β) := by
  induction ψ <;> simp [mapSubtype, Sat] at p_sat ⊢ <;> grind
end LeanModelChecking.PositiveBool
