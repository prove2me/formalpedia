-- Prove2me | solution 1 for LTree.nonempty_of_isShattered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:33:29.248839+00:00
-- url     : https://prove2.me/submissions/12991ba7-0056-48e1-9126-29c5eed12e6d

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra

set_option autoImplicit true
@[expose] public section
public section
namespace LTree
theorem _root_.solution {X : Type} {C : ConceptClass X Bool}
    {n : ℕ} (T : LTree X n) (hT : T.isShattered C) : C.Nonempty := by
  induction n with
  | zero => match T with | .leaf => exact hT
  | succ k _ =>
    match T with
    | .branch _ _ _ =>
      obtain ⟨⟨c, hc, _⟩, _⟩ := hT
      exact ⟨c, hc⟩
end LTree
