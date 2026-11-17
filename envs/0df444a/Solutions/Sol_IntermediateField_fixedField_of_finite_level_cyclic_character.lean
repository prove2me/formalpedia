-- Prove2me | solution 1 for IntermediateField.fixedField_of_finite_level_cyclic_character
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:13.777766+00:00
-- url     : https://prove2.me/submissions/f82571d6-c44d-42fd-b3b4-cc47064e439f

import Mathlib

set_option autoImplicit false

namespace IntermediateField

/-- A surjective finite-level character into a finite cyclic group cuts out
the expected finite cyclic extension. The level proves that its kernel is
closed in the Krull topology. -/
theorem _root_.solution
    {K L G : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [Group G] [Finite G] [IsCyclic G]
    (f : (L ≃ₐ[K] L) →* G) (hf : Function.Surjective f)
    (hlevel : ∃ E : IntermediateField K L,
      FiniteDimensional K E ∧ E.fixingSubgroup ≤ f.ker) :
    FiniteDimensional K (fixedField f.ker) ∧
      IsGalois K (fixedField f.ker) ∧
      IsCyclic ((fixedField f.ker) ≃ₐ[K] (fixedField f.ker)) ∧
      Module.finrank K (fixedField f.ker) = Nat.card G := by
  obtain ⟨E, hE, hker⟩ := hlevel
  letI := hE
  have hopen : IsOpen (f.ker : Set (L ≃ₐ[K] L)) :=
    Subgroup.isOpen_mono hker (fixingSubgroup_isOpen E)
  let H : ClosedSubgroup (L ≃ₐ[K] L) :=
    ⟨f.ker, f.ker.isClosed_of_isOpen hopen⟩
  have hfix : (fixedField f.ker).fixingSubgroup = f.ker :=
    InfiniteGalois.fixingSubgroup_fixedField H
  have hfinite : FiniteDimensional K (fixedField f.ker) := by
    apply (InfiniteGalois.isOpen_iff_finite _).mp
    rwa [hfix]
  letI := hfinite
  letI : IsGalois K (fixedField f.ker) :=
    IsGalois.of_fixedField_normal_subgroup f.ker
  let e : ((fixedField f.ker) ≃ₐ[K] (fixedField f.ker)) ≃* G :=
    (InfiniteGalois.normalAutEquivQuotient H).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hcyclic : IsCyclic ((fixedField f.ker) ≃ₐ[K] (fixedField f.ker)) :=
    isCyclic_of_injective e.toMonoidHom e.injective
  refine ⟨hfinite, inferInstance, hcyclic, ?_⟩
  rw [← IsGalois.card_aut_eq_finrank]
  exact Nat.card_congr e.toEquiv

end IntermediateField
