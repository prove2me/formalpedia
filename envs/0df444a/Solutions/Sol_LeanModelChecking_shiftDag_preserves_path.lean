-- Prove2me | solution 1 for LeanModelChecking.shiftDag.preserves_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:21.055327+00:00
-- url     : https://prove2.me/submissions/da7fdc63-e0ed-413c-b908-c0abd27fe81c

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
open LeanModelChecking.shiftDag
variable
  {T : Type} [PartialOrder T]
  {φ₁ φ₂ : T} (hle : φ₁ ≤ φ₂)
variable (r₁ : {q // q ≤ φ₁}) (r₂ : {q // q ≤ φ₂}) (G : DAG (Iic φ₁))
namespace LeanModelChecking.shiftDag
theorem _root_.solution
  (G : DAG (Iic φ₁)) (hrx : (r₁, 0) ∈ G.V)
  (p : ℕ → Iic φ₂) (p_path : (dag hle r₁ r₂ G hrx).path p)
    : G.path (fun i => ⟨(p (i + 1)).val,
        path_after_1_prop hle r₁ r₂ G hrx p p_path _ (by omega)⟩) := by
  simp only [DAG.path] at p_path
  obtain ⟨n, p_path⟩ := p_path
  simp only [DAG.path]
  exists n
  grind [dag]
end LeanModelChecking.shiftDag
