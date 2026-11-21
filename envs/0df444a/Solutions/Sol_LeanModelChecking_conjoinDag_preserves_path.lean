-- Prove2me | solution 1 for LeanModelChecking.conjoinDag.preserves_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:24.646638+00:00
-- url     : https://prove2.me/submissions/fbe42b87-a06f-445a-9c0d-90015ad95826

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
open LeanModelChecking.conjoinDag
variable
  {T : Type} [PartialOrder T] [DecidableEq T]
  {φ₁ φ₂ Φ : T}
  (leφ₁ : φ₁ ≤ Φ) (leφ₂ : φ₂ ≤ Φ)
variable
  (r₁ : Iic φ₁) (r₂ : Iic φ₂) (R : Iic Φ)
  (G₁ : DAG (Iic φ₁)) (G₂ : DAG (Iic φ₂))
namespace LeanModelChecking.conjoinDag
theorem _root_.solution
  (op : ℕ → Iic Φ) (op_path : (dag leφ₁ leφ₂ r₁ r₂ R G₁ G₂).path op)
  : (∃ k, (Subtype.val <$> G₁).path (fun i => (op (k + i)).val))
      ∨ (Subtype.val <$> G₂).path (fun i => (op (i + 1)).val) := by
  obtain ⟨n, op_path⟩ := op_path
  by_cases h_all_not_G₁ : ∀ i, ((op (1 + i)).val, n + 1 + i) ∉ (Subtype.val <$> G₁).V
  · right
    simp [Functor.map] at h_all_not_G₁
    exists n + 1
    intros i
    specialize op_path (i + 1)
    rcases op_path with (op_path|op_path)|op_path
    · exfalso; cases G₁; grind
    · simp [Functor.map]; grind
    · grind
  · left
    simp only [Functor.map, Set.mem_image, Prod.mk.injEq, Prod.exists, exists_eq_right_right,
      Subtype.exists, exists_and_right, exists_eq_right, not_exists, not_forall, not_not
      ] at h_all_not_G₁
    obtain ⟨k, entry_p, entry_V₁⟩ := h_all_not_G₁
    suffices ∀ i, (((op (1 + k + i)).val, n + 1 + k + i), (op (1 + k + (i + 1))).val) ∈
        (Subtype.val <$> G₁).E by exists 1 + k; exists n + 1 + k
    simp only [Functor.map, Set.mem_image, Prod.mk.injEq, Prod.exists, Subtype.exists,
      exists_and_right, exists_eq_right_right, exists_eq_right]
    intros i
    induction i
    · simp only [add_zero, zero_add]
      specialize op_path (1 + k)
      simp only [dag, base, Functor.map] at op_path
      rcases op_path with (op_path|op_path)|op_path <;> grind
    next i ih =>
      specialize op_path (1 + k + (i + 1))
      simp only [dag, base, Functor.map] at op_path
      rcases op_path with (op_path|op_path)|op_path
      · grind
      · exfalso; cases G₁; grind
      · exfalso; grind
end LeanModelChecking.conjoinDag
