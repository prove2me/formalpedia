-- Prove2me | solution 1 for LeanModelChecking.DAG.path_elems_prop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:44.806819+00:00
-- url     : https://prove2.me/submissions/0d33bc67-05e8-4a37-be33-8d7de83c09ef

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
open LeanModelChecking.DAG
namespace LeanModelChecking.DAG
theorem _root_.solution {α} {P : α → Prop} {G : DAG (Subtype P)} {p : ℕ
    → α} (p_path : (Subtype.val <$> G).path p) : ∀ i, P (p i) := by
  simp [DAG.path, Functor.map] at p_path
  grind
end LeanModelChecking.DAG
