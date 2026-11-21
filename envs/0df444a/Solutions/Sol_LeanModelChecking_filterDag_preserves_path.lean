-- Prove2me | solution 1 for LeanModelChecking.filterDag.preserves_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:25.085355+00:00
-- url     : https://prove2.me/submissions/7405cf6d-7b64-40c1-845f-398784d99c45

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
open LeanModelChecking.filterDag
variable
  {T : Type} [PartialOrder T]
  {φ Φ : T}
  (leφ : φ ≤ Φ)
variable (G : DAG (Iic Φ)) (rΦ : Iic Φ) (rφ : Iic φ) (shift : ℕ)
namespace LeanModelChecking.filterDag
theorem _root_.solution {p : ℕ → Iic φ} (p_path : (dag leφ G rΦ rφ shift).path p) : G.path (fun i =>
    (p (i + 1)).embedLe leφ) := by
  obtain ⟨start, p_path⟩ := p_path
  exists shift + start + 1
  intros i
  specialize p_path (i + 1)
  grind [dag]
end LeanModelChecking.filterDag
