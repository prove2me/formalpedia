-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.existsUnique_extension_hom_of_genericFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/92565d7f-8425-5be0-998d-a8dacff77f3b

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_existsUnique_extension_hom_of_genericFibre
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (LA : RelativeGroupLaw R f)
    {t : T ⟶ Spec (CommRingCat.of R)} [Smooth t] (LT : RelativeGroupLaw R t)
    (φK : SchemeHomOver (RelativeGroupLaw.genericFibreStr K t) (RelativeGroupLaw.genericFibreStr K f))
    (hφK : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K t)),
        NeronModelInfra.schemeHomOverComp ((LT.genericFibre K).mul s x y) φK =
          (LA.genericFibre K).mul s (NeronModelInfra.schemeHomOverComp x φK)
            (NeronModelInfra.schemeHomOverComp y φK)) :
    ∃! φ : SchemeHomOver t f,
      genericFibreRestrict R K f t φ = φK ∧
      ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s t),
        NeronModelInfra.schemeHomOverComp (LT.mul s x y) φ =
          LA.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ) := by

  have hN := NeronModelPropertyBundle.of_abelianSchemePropertyBundle R K hA
  have hbij := hN.neronMapping T t inferInstance
  obtain ⟨φ, rfl⟩ := hbij.2 φK
  haveI := hA.proper

  have hgen : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver (s ≫ specGenericFibreInclusion R K) t),
      (LT.mul _ x y).1 ≫ φ.1 =
        (LA.mul _ ⟨x.1 ≫ φ.1, by rw [Category.assoc, φ.2, x.2]⟩
          ⟨y.1 ≫ φ.1, by rw [Category.assoc, φ.2, y.2]⟩).1 := by
    intro S s x y
    have h := congrArg (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K))
      (hφK s (RelativeGroupLaw.baseChangePointOfBase _ x) (RelativeGroupLaw.baseChangePointOfBase _ y))
    simp only [RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict,
      RelativeGroupLaw.genericFibre, RelativeGroupLaw.baseChangePointToBase_mul,
      RelativeGroupLaw.baseChangePointToBase_ofBase] at h
    exact congrArg Subtype.val h

  have hhom : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s t),
      NeronModelInfra.schemeHomOverComp (LT.mul s x y) φ =
        LA.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ) := by
    intro S s x y
    apply Subtype.ext
    exact RelativeGroupLaw.comp_mul_eq_mul_comp_of_genericFibre R K LA LT φ hgen s x y
  exact ⟨φ, ⟨rfl, hhom⟩, fun ψ hψ => hbij.1 hψ.1⟩

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_existsUnique_extension_hom_of_genericFibre
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_existsUnique_extension_hom_of_genericFibre (solution)
