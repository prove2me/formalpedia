-- Prove2me | solution 1 for LeanModelChecking.subtype_val_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:33.667978+00:00
-- url     : https://prove2.me/submissions/157647b8-24ee-4249-a34d-1eed71231aa9

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
namespace LeanModelChecking
theorem _root_.solution {α} {P : α → Prop} :
    @Function.Injective (Subtype P) α Subtype.val := by simp
end LeanModelChecking
