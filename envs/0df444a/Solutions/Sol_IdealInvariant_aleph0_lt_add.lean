-- Prove2me | solution 1 for IdealInvariant.aleph0_lt_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:26:51.310557+00:00
-- url     : https://prove2.me/submissions/b97aa5f8-3f03-4685-981c-5ff16542cb9b

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
theorem _root_.solution (hσ : ∀ 𝒜 ⊆ I, 𝒜.Countable → ⋃₀ 𝒜 ∈ I) (hI : ∃ 𝒜 ⊆ I, ⋃₀ 𝒜 ∉ I) :
    ℵ₀ < add I := by
  obtain ⟨𝒜, h𝒜, hU⟩ := hI
  have : Nonempty {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 ∉ I} := ⟨⟨𝒜, h𝒜, hU⟩⟩
  obtain ⟨⟨ℬ, hℬ, hV⟩, h⟩ :=
    ciInf_mem fun 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 ∉ I} ↦ #𝒜.1
  rw [add, ← h]
  exact not_le.1 fun hle ↦ hV (hσ ℬ hℬ (le_aleph0_iff_set_countable.1 hle))
end IdealInvariant
