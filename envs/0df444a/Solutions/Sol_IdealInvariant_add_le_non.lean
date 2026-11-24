-- Prove2me | solution 1 for IdealInvariant.add_le_non
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:27:00.809734+00:00
-- url     : https://prove2.me/submissions/6f2308b0-de63-4136-a5e4-c6c7cf11576e

module
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AddUN_IdealInvariant
public import Theorems.Thm_IdealInvariant_add_le
public import Theorems.Thm_IdealInvariant_exists_notMem_mk_eq_non

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Set
open IdealInvariant
variable {X : Type u} {I : Set (Set X)} {𝒜 : Set (Set X)} {A : Set X}
namespace IdealInvariant
theorem _root_.solution (hsing : ∀ x, {x} ∈ I) (hI : ∃ A, A ∉ I) : add I ≤ non I := by
  obtain ⟨A, hA, hcard⟩ := exists_notMem_mk_eq_non hI
  have hU : ⋃₀ ((fun x ↦ ({x} : Set X)) '' A) = A := by
    ext y
    simp
  rw [← hcard]
  refine (add_le ?_ (by rwa [hU])).trans mk_image_le
  rintro _ ⟨x, -, rfl⟩
  exact hsing x
end IdealInvariant
