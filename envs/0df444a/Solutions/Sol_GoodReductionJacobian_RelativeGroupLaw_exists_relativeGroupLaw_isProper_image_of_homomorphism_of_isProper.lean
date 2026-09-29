-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_isProper_image_of_homomorphism_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d24df63e-7ccc-5c8a-87a4-f21310d36167

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_isProper_image_of_homomorphism_of_isProper

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    {k : Type u} [Field k]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)} [IsSeparated f] [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)
    {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of k)} [IsProper g] (LX : RelativeGroupLaw k g) (σ : SchemeHomOver g f)
    (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ)) :
    ∃ LB : RelativeGroupLaw k (σ.1.imageι ≫ f),
      IsProper (σ.1.imageι ≫ f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)),
        NeronModelInfra.schemeHomOverComp (LB.mul t x y) (⟨σ.1.imageι, rfl⟩ : SchemeHomOver (σ.1.imageι ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x ⟨σ.1.imageι, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨σ.1.imageι, rfl⟩)) ∧
      ((∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x) →
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)),
          LB.mul t x y = LB.mul t y x) := by

  have hg : σ.1 ≫ f = g := σ.2
  haveI : IsProper (σ.1 ≫ f) := by rw [hg]; infer_instance
  haveI : IsProper σ.1 := IsProper.of_comp σ.1 f

  haveI : Flat g := inferInstance
  haveI : Flat (σ.1.imageι ≫ f) := inferInstance
  obtain ⟨LB, hLB, hcomm⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_image_of_homomorphism_of_flat L LX σ hσ
  refine ⟨LB, ?_, hLB, hcomm⟩

  haveI : UniversallyClosed (σ.1.toImage ≫ σ.1.imageι ≫ f) := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hg]; infer_instance
  haveI : UniversallyClosed (σ.1.imageι ≫ f) := UniversallyClosed.of_comp_surjective σ.1.toImage _
  exact ⟨⟩

#print axioms solution

end S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_isProper_image_of_homomorphism_of_isProper
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_isProper_image_of_homomorphism_of_isProper (solution)
