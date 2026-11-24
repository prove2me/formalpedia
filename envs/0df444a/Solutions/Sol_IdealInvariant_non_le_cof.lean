-- Prove2me | solution 1 for IdealInvariant.non_le_cof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:27:59.380833+00:00
-- url     : https://prove2.me/submissions/bb3780f1-f468-42a2-84c7-22e8f1e71b6d

module
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AddUN_IdealInvariant
public import Theorems.Thm_IdealInvariant_non_le
public import Theorems.Thm_IdealInvariant_exists_cofinal_mk_eq_cof

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Set
open IdealInvariant
variable {X : Type u} {I : Set (Set X)} {𝒜 : Set (Set X)} {A : Set X}
namespace IdealInvariant
theorem _root_.solution (huniv : univ ∉ I) : non I ≤ cof I := by
  obtain ⟨𝒜, h𝒜, hcof, hcard⟩ := exists_cofinal_mk_eq_cof I
  have hne : ∀ B : 𝒜, ∃ x, x ∉ B.1 := fun B ↦ by
    by_contra h
    push Not at h
    exact huniv (eq_univ_of_forall h ▸ h𝒜 B.2)
  choose f hf using hne
  have hrange : range f ∉ I := fun h ↦ by
    obtain ⟨B, hB, hsub⟩ := hcof _ h
    exact hf ⟨B, hB⟩ (hsub ⟨⟨B, hB⟩, rfl⟩)
  rw [← hcard]
  exact (non_le hrange).trans mk_range_le
end IdealInvariant
