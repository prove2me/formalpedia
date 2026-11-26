-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.compSetoid_ofSubtype_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:19:41.683168+00:00
-- url     : https://prove2.me/submissions/2fdaa650-e4bd-4c6f-986d-459bfc902baa

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_le
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_left
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_right

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
variable (p : D → Prop) [DecidablePred p]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (σ α : Perm (Subtype p)) (a b : Subtype p) :
    compSetoid σ α a b ↔ compSetoid (ofSubtype σ) (ofSubtype α) a.1 b.1 := by
  constructor
  · intro h
    have := compSetoid_le (Setoid.comap Subtype.val (compSetoid (ofSubtype σ) (ofSubtype α)))
      (fun z => by
        rw [Setoid.comap_rel, ← ofSubtype_apply_coe]
        exact compSetoid_left _ _ _)
      (fun z => by
        rw [Setoid.comap_rel, ← ofSubtype_apply_coe]
        exact compSetoid_right _ _ _) h
    rwa [Setoid.comap_rel] at this
  · intro h
    let g : D → Quotient (compSetoid σ α) ⊕ D := fun u =>
      if hu : p u then Sum.inl (Quotient.mk _ ⟨u, hu⟩) else Sum.inr u
    have key : ∀ (π : Perm (Subtype p)), (∀ z, compSetoid σ α z (π z)) →
        ∀ z, Setoid.ker g z (ofSubtype π z) := by
      intro π hπ z
      rw [Setoid.ker_def]
      by_cases hz : p z
      · have h1 : ofSubtype π z = (π ⟨z, hz⟩).1 := ofSubtype_apply_of_mem π hz
        have h2 : p (ofSubtype π z) := h1 ▸ (π ⟨z, hz⟩).2
        simp only [g, hz, h2, ↓reduceDIte]
        congr 1
        apply Quotient.sound
        have : (⟨ofSubtype π z, h2⟩ : Subtype p) = π ⟨z, hz⟩ := Subtype.ext h1
        rw [this]
        exact hπ _
      · rw [ofSubtype_apply_of_not_mem π hz]
    have := compSetoid_le (Setoid.ker g) (key σ (compSetoid_left σ α))
      (key α (compSetoid_right σ α)) h
    rw [Setoid.ker_def] at this
    simp only [g, a.2, b.2, ↓reduceDIte, Sum.inl.injEq] at this
    exact Quotient.exact this
end LeanPool.K5MinorFreeChoosability
