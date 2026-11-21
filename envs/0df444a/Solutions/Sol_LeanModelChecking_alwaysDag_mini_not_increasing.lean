-- Prove2me | solution 1 for LeanModelChecking.alwaysDag.mini_not_increasing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:10.312183+00:00
-- url     : https://prove2.me/submissions/d415d41f-e851-4681-9cae-5040385ea8ef

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
open LeanModelChecking.alwaysDag
variable
  {T : Type} [PartialOrder T]
  {φ Φ : T}
  (ltφ : φ < Φ)
variable (G : ℕ → DAG (Iic φ))
namespace LeanModelChecking.alwaysDag
theorem _root_.solution q l q' (He : ((q.embedLe ltφ.le, l),
    q'.embedLe ltφ.le) ∈ E G) : mini G (q', l + 1) ≤ mini G (q, l) := by
  obtain ⟨HVb, _, _, He⟩ :
      (q, l) ∈ Vb G ∧ (q' : T) ≤ φ ∧ (q : T) ≤ φ ∧
        ((q, l - mini G (q, l)), q') ∈ (G (mini G (q, l))).E := by
    simpa [E, show q ≠ Φ by grind] using He
  have ec := (G (mini G (q, l))).edge_closure _ He
  simp at ec
  apply csInf_le ⟨0, by intro i _; exact Nat.zero_le i⟩
  simp
  have := mini_le _ _ _ HVb
  grind
end LeanModelChecking.alwaysDag
