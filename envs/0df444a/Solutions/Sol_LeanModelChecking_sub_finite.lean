-- Prove2me | solution 1 for LeanModelChecking.sub_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:36.596774+00:00
-- url     : https://prove2.me/submissions/ed3a80f7-837a-4ffb-9c82-b39a95ffbe0b

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_mem_sub_finset

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
theorem _root_.solution {AP} (f : NNF AP) : Finite { q // q ≤ f } := by
  classical
  refine Finite.of_injective (fun q => (⟨q.1, ?_⟩ : { r // r ∈ subFinset f })) ?_
  · exact mem_sub_finset q.2
  · intro a b h; grind
end LeanModelChecking
