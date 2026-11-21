-- Prove2me | solution 1 for LeanModelChecking.replaceRoot.runDag_accepting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:50.993242+00:00
-- url     : https://prove2.me/submissions/de38c596-8576-4916-9aac-95c036c4b05e

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Theorems.Thm_LeanModelChecking_replaceRoot_preserves_path

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.replaceRoot
variable
  {T : Type} [PartialOrder T] [DecidableEq T]
  {φ₁ φ₂ : T} (hle : φ₁ ≤ φ₂)
namespace LeanModelChecking.replaceRoot
theorem _root_.solution
  {S}
  {M : ABW S (Iic φ₁)} {M' : ABW S (Iic φ₂)} {w : ℕ → S}
  {G : RunDAG M w} (G_acc : G.accepting)
  (h_delta_root : ∀ Q, PositiveBool.Sat Q (M.δ M.q₀ (w 0))
      → PositiveBool.Sat ((Subtype.embedLe hle) '' Q) (M'.δ M'.q₀ (w 0)))
  (h_delta_eq : ∀ (q : Iic φ₁) i,
      M'.δ (q.embedLe hle) (w i) = (M.δ q (w i)).mapSubtypeImp (fun _ p => p.trans hle))
  (hF : ∀ q : Iic φ₁, q.embedLe hle ∈ M'.F ↔ q ∈ M.F)
    : (runDag hle G h_delta_root h_delta_eq).accepting := by
  intros p p_path
  have p_path' := preserves_path hle M.q₀ M'.q₀ G.toDAG p p_path
  intros i
  obtain ⟨j, hj, H⟩ := G_acc _ p_path' i
  refine ⟨j + 1, by omega, ?_⟩
  have := (hF _).mpr H
  rwa [show Subtype.embedLe hle _ = p (j + 1) from rfl] at this
end LeanModelChecking.replaceRoot
