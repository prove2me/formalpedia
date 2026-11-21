-- Prove2me | solution 1 for LeanModelChecking.mem_sub_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:10.985179+00:00
-- url     : https://prove2.me/submissions/8b696a35-7bd5-4674-a1fb-343c7f97d045

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
theorem _root_.solution {AP} [DecidableEq AP] {q f : NNF AP} : q ≤ f → q ∈ subFinset f := by
  intro h; induction h
  { cases q <;> grind [subFinset] }
  all_goals grind [subFinset]
end LeanModelChecking
