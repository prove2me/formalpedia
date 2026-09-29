-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isInfinitesimal_map_schemeHomOverComp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f7f488f2-9e0e-56ff-95c7-6fd71bbddaed

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isInfinitesimal_map_schemeHomOverComp

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    {D C : Type} [CommRing D] [Algebra B D] [CommRing C] [Algebra B C] (φ : D →ₐ[B] C)
    (J : Ideal D) (Q : SchemeHomOver (Scheme.specOver (𝒪 := B) D) f) (hQ : L.IsInfinitesimal J Q) :
    L.IsInfinitesimal (J.map φ)
      (schemeHomOverComp (Spec.map (CommRingCat.ofHom φ.toRingHom)) (Scheme.specMap_algHom_comp_specOver φ) Q) := by

  let ψ : (D ⧸ J) →ₐ[B] (C ⧸ J.map φ) :=
    Ideal.quotientMapₐ (J.map φ) φ Ideal.le_comap_map
  have hcomm : (Ideal.Quotient.mkₐ B (J.map φ)).comp φ = ψ.comp (Ideal.Quotient.mkₐ B J) := by
    apply AlgHom.ext; intro x; rfl
  unfold RelativeGroupLaw.IsInfinitesimal at hQ ⊢

  have key : schemeHomOverComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B (J.map φ)).toRingHom))
      (Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B (J.map φ)))
      (schemeHomOverComp (Spec.map (CommRingCat.ofHom φ.toRingHom)) (Scheme.specMap_algHom_comp_specOver φ) Q) =
    schemeHomOverComp (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (Scheme.specMap_algHom_comp_specOver ψ)
      (schemeHomOverComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom))
        (Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B J)) Q) := by
    apply Subtype.ext
    simp only [schemeHomOverComp_coe, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [key, hQ]
  exact L.one_natural _ _ _ _

end S_GoodReductionJacobian_RelativeGroupLaw_isInfinitesimal_map_schemeHomOverComp
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isInfinitesimal_map_schemeHomOverComp (solution)
