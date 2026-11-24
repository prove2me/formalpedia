-- Prove2me | solution 1 for IdealInvariant.exists_cofinal_mk_eq_cof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:26:50.648433+00:00
-- url     : https://prove2.me/submissions/13c47fb5-768b-4e77-b464-9471d2f59804

module
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AddUN_IdealInvariant

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Set
open IdealInvariant
variable {X : Type u} {I : Set (Set X)} {𝒜 : Set (Set X)} {A : Set X}
namespace IdealInvariant
theorem _root_.solution (I : Set (Set X)) :
    ∃ 𝒜 ⊆ I, (∀ A ∈ I, ∃ B ∈ 𝒜, A ⊆ B) ∧ #𝒜 = cof I := by
  have : Nonempty {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ∀ A ∈ I, ∃ B ∈ 𝒜, A ⊆ B} :=
    ⟨⟨I, Subset.rfl, fun A hA ↦ ⟨A, hA, Subset.rfl⟩⟩⟩
  obtain ⟨⟨𝒜, h𝒜, hcof⟩, h⟩ :=
    ciInf_mem fun 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ∀ A ∈ I, ∃ B ∈ 𝒜, A ⊆ B} ↦ #𝒜.1
  exact ⟨𝒜, h𝒜, hcof, h⟩
end IdealInvariant
