-- Prove2me | solution 1 for LeanModelChecking.PositiveBool.sat_map_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:32.982186+00:00
-- url     : https://prove2.me/submissions/1ccf996f-5fc7-49d3-9388-1c9c99d63f2c

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
  {T : Type} [PartialOrder T] {Q' Q : T} (hq : Q' ≤ Q)
  {ψ : PositiveBool T} {Y : Set { q // q ≤ Q' }}
  (H2 : Forall (fun x => x ≤ Q') ψ)
    : (ψ.mapSubtype H2).Sat Y
        ↔ (ψ.mapSubtype (H2.imp (by grind))).Sat (Subtype.embedLe hq '' Y) := by
  induction ψ <;> simp [Sat, mapSubtype] <;> simp [Forall] at H2 <;> grind
end LeanModelChecking.PositiveBool
