-- Prove2me | solution 1 for GoodReductionJacobian.exists_schemeHomOver_inverse_of_abelianSchemePropertyBundle_of_genericFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/99de02b6-bd34-5548-bc9a-2d194a5dd76c

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_exists_schemeHomOver_inverse_of_abelianSchemePropertyBundle_of_genericFibre
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace Sub1

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]

theorem genericFibreRestrict_comp_coe {A₁ A₂ A₃ : Scheme.{u}}
    {f₁ : A₁ ⟶ Spec (CommRingCat.of R)} {f₂ : A₂ ⟶ Spec (CommRingCat.of R)} {f₃ : A₃ ⟶ Spec (CommRingCat.of R)}
    (φ : SchemeHomOver f₁ f₂) (ψ : SchemeHomOver f₂ f₃) :
    (genericFibreRestrict R K f₃ f₁ ⟨φ.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, φ.2]⟩).1
      = (genericFibreRestrict R K f₂ f₁ φ).1 ≫ (genericFibreRestrict R K f₃ f₂ ψ).1 := by
  apply pullback.hom_ext
  · simp only [genericFibreRestrict, pullback.lift_fst, Category.assoc, pullback.lift_fst_assoc]
  · simp only [genericFibreRestrict, pullback.lift_snd, Category.assoc]

theorem genericFibreRestrict_id_coe {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} :
    (genericFibreRestrict R K f f ⟨𝟙 A, Category.id_comp f⟩).1 = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [genericFibreRestrict, pullback.lift_fst, Category.comp_id, Category.id_comp]
  · simp only [genericFibreRestrict, pullback.lift_snd, Category.id_comp]

end Sub1

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {A₁ A₂ : Scheme.{u}} {f₁ : A₁ ⟶ Spec (CommRingCat.of R)} {f₂ : A₂ ⟶ Spec (CommRingCat.of R)}
    (h₁ : AbelianSchemePropertyBundle R f₁) (h₂ : AbelianSchemePropertyBundle R f₂)
    (φK : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K))
      (pullback.snd f₂ (specGenericFibreInclusion R K)))
    (ψK : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K))
      (pullback.snd f₁ (specGenericFibreInclusion R K)))
    (hφψ : φK.1 ≫ ψK.1 = 𝟙 _) (hψφ : ψK.1 ≫ φK.1 = 𝟙 _) :
    ∃ (φ : SchemeHomOver f₁ f₂) (ψ : SchemeHomOver f₂ f₁),
      genericFibreRestrict R K f₂ f₁ φ = φK ∧ genericFibreRestrict R K f₁ f₂ ψ = ψK ∧
      φ.1 ≫ ψ.1 = 𝟙 A₁ ∧ ψ.1 ≫ φ.1 = 𝟙 A₂ ∧
      (∀ φ' : SchemeHomOver f₁ f₂, genericFibreRestrict R K f₂ f₁ φ' = φK → φ' = φ) := by
  have hN₁ := NeronModelInfra.NeronModelPropertyBundle.of_abelianSchemePropertyBundle R K h₁
  have hN₂ := NeronModelInfra.NeronModelPropertyBundle.of_abelianSchemePropertyBundle R K h₂

  have s₂₁ := hN₂.neronMapping A₁ f₁ h₁.smooth
  have s₁₂ := hN₁.neronMapping A₂ f₂ h₂.smooth
  have s₁₁ := hN₁.neronMapping A₁ f₁ h₁.smooth
  have s₂₂ := hN₂.neronMapping A₂ f₂ h₂.smooth
  obtain ⟨φ, hφ⟩ := s₂₁.2 φK
  obtain ⟨ψ, hψ⟩ := s₁₂.2 ψK
  refine ⟨φ, ψ, hφ, hψ, ?_, ?_, fun φ' hφ' => s₂₁.1 (hφ'.trans hφ.symm)⟩
  · have h : genericFibreRestrict R K f₁ f₁ ⟨φ.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, φ.2]⟩
        = genericFibreRestrict R K f₁ f₁ ⟨𝟙 A₁, Category.id_comp f₁⟩ := by
      apply Subtype.ext
      rw [Sub1.genericFibreRestrict_comp_coe, Sub1.genericFibreRestrict_id_coe, hφ, hψ, hφψ]
    exact congrArg Subtype.val (s₁₁.1 h)
  · have h : genericFibreRestrict R K f₂ f₂ ⟨ψ.1 ≫ φ.1, by rw [Category.assoc, φ.2, ψ.2]⟩
        = genericFibreRestrict R K f₂ f₂ ⟨𝟙 A₂, Category.id_comp f₂⟩ := by
      apply Subtype.ext
      rw [Sub1.genericFibreRestrict_comp_coe, Sub1.genericFibreRestrict_id_coe, hφ, hψ, hψφ]
    exact congrArg Subtype.val (s₂₂.1 h)

end S_GoodReductionJacobian_exists_schemeHomOver_inverse_of_abelianSchemePropertyBundle_of_genericFibre
end P2MW
export P2MW.S_GoodReductionJacobian_exists_schemeHomOver_inverse_of_abelianSchemePropertyBundle_of_genericFibre (solution)
