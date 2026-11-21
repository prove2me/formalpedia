-- Prove2me | solution 1 for LeanModelChecking.replaceRoot.preserves_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:24.161335+00:00
-- url     : https://prove2.me/submissions/46ed5650-7ed6-49a3-abbe-f4f474df186e

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
open LeanModelChecking.replaceRoot
variable
  {T : Type} [PartialOrder T] [DecidableEq T]
  {φ₁ φ₂ : T} (hle : φ₁ ≤ φ₂)
variable (r₁ : Iic φ₁) (r₂ : Iic φ₂) (G : DAG (Iic φ₁))
namespace LeanModelChecking.replaceRoot
theorem _root_.solution
  (p : ℕ → {q // q ≤ φ₂}) (p_path : (dag hle r₁ r₂ G).path p)
    : G.path (fun i => ⟨(p (i + 1)).val, path_after_1_prop hle r₁ r₂ G p p_path _ (by omega)⟩) := by
  simp only [DAG.path] at p_path
  obtain ⟨n, p_path⟩ := p_path
  simp only [DAG.path]
  exists (n + 1)
  intros i
  specialize p_path (i + 1)
  simp [dag, base] at p_path
  grind
end LeanModelChecking.replaceRoot
