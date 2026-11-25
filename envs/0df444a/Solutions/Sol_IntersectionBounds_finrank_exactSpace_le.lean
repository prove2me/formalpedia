-- Prove2me | solution 1 for IntersectionBounds.finrank_exactSpace_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:50:05.505396+00:00
-- url     : https://prove2.me/submissions/41877bb9-ab52-40f7-a0c8-e3e8dbf940bd

module
public import Definitions.Def_IntersectionBounds_EvaluationSpace
public import Definitions.Def_IntersectionBounds_Definitions
public import Definitions.Def_IntersectionBounds_UniformSpace
public import Theorems.Thm_IntersectionBounds_indicator_empty
attribute [local simp] IntersectionBounds.indicator_empty



set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} [Fintype V] {K : Type v} [Field K]
variable (F : Finset (Finset V))
namespace IntersectionBounds
theorem _root_.solution (s : ℕ) :
    Module.finrank K (exactSpace F s : Submodule K (F → K)) ≤ (Fintype.card V).choose s := by
  classical
  let I := {T : Finset V // T.card = s}
  let gen : I → (F → K) := fun T => indicator F T.val
  have heq : exactSpace F s = span K (Set.range gen) := by
    apply congrArg (span K)
    ext f
    constructor
    · rintro ⟨T, hT, rfl⟩
      exact ⟨⟨T, hT⟩, rfl⟩
    · rintro ⟨T, rfl⟩
      exact ⟨T.val, T.property, rfl⟩
  rw [heq]
  calc
    _ ≤ Fintype.card I := finrank_range_le_card gen
    _ = (Fintype.card V).choose s := by
      rw [Fintype.card_subtype]
      have hsets : univ.filter (fun T : Finset V => T.card = s) =
          (univ : Finset V).powersetCard s := by
        ext T
        simp
      rw [hsets, Finset.card_powersetCard, Finset.card_univ]
end IntersectionBounds
