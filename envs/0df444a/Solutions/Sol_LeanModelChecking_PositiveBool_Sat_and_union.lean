-- Prove2me | solution 1 for LeanModelChecking.PositiveBool.Sat.and_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:05.773954+00:00
-- url     : https://prove2.me/submissions/7dc3e7ef-5547-447b-9667-0699a5c2d1b5

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_PositiveBool_Sat_monotone


set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.PositiveBool
namespace LeanModelChecking.PositiveBool
namespace Sat
theorem _root_.solution {Q} (f g : PositiveBool Q) {A B : Set Q} : PositiveBool.Sat A f
    → PositiveBool.Sat B g → PositiveBool.Sat (A ∪ B) (f.and g) := by
  intros HA HB
  simp only [Sat]
  constructor
  · apply Sat.monotone Set.subset_union_left; assumption
  · apply Sat.monotone Set.subset_union_right; assumption
end Sat
end LeanModelChecking.PositiveBool
