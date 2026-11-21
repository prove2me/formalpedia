-- Prove2me | solution 1 for LeanModelChecking.release_mp.left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:47:58.895768+00:00
-- url     : https://prove2.me/submissions/88e25575-befd-465a-8780-4322b133798a

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_subformula_toABW_lang

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.release_mp
variable {S} {φ₁ φ₂ : NNF S} {w : ℕ → Letter S} {G : RunDAG (φ₁.release φ₂).toABW w}
namespace LeanModelChecking.release_mp
theorem _root_.solution (G_acc : G.accepting) {l} (H₁ : (⟨φ₁.release φ₂, le_refl _⟩, l) ∈
    G.V) (H₂ : (⟨φ₁.release φ₂, le_refl _⟩,
    l + 1) ∉ G.V) : φ₁.toABW.language (fun j => w (j + l)) := by
  obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ H₁
  rcases p_sat with ⟨_, p_sat|p_sat⟩
  · apply subformula_toABW_lang (sub.release_left sub.refl) G_acc p_sat p_sub
  · exfalso
    have := G.edge_closure
    simp [PositiveBool.mapSubtype, PositiveBool.Sat] at p_sat
    have : ((⟨φ₁.release φ₂, le_refl _⟩, l), ⟨φ₁.release φ₂, le_refl _⟩) ∈ G.E := by grind
    grind
end LeanModelChecking.release_mp
