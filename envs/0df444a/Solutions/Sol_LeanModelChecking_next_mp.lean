-- Prove2me | solution 1 for LeanModelChecking.next_mp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:48:22.746125+00:00
-- url     : https://prove2.me/submissions/eba38662-2197-4e62-972a-84df6adf5fb8

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_subformula_toABW_lang
public import Theorems.Thm_LeanModelChecking_and_mp_right
public import Theorems.Thm_LeanModelChecking_or_mpr_right

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
theorem _root_.solution {AP : Type} {φ : NNF AP} {w} : φ.next.toABW.language w
    → φ.toABW.language (fun j => w (j + 1)) := by
  rintro ⟨G, G_acc⟩
  have in_1 : (⟨φ, sub.next sub.refl⟩, 1) ∈ G.V := by
    have := G.p_sat _ G.p_root
    simp only [NNF.toABW, delta, PositiveBool.mapSubtype, PositiveBool.Sat] at this
    rcases this with ⟨Y, p_sat, p_sub⟩
    have := G.edge_closure ((⟨φ.next, le_refl _⟩, 0), ⟨φ, sub.next sub.refl⟩)
    refine (this ?_).right
    apply p_sub
    grind
  obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ in_1
  apply subformula_toABW_lang (sub.next sub.refl) G_acc p_sat p_sub
end LeanModelChecking
