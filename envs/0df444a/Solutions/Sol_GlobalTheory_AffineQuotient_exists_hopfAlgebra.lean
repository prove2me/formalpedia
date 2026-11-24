-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.exists_hopfAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:56:35.560946+00:00
-- url     : https://prove2.me/submissions/f0ec7c9a-31f6-43ec-b513-443c071a145c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AffineQuotient
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.AffineQuotient
theorem _root_.solution (R : Type) [CommRing R] [IsNoetherianRing R]
    (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [IsFinite H.hom] [Flat H.hom] :
    ∃ (Λ : Type) (_ : CommRing Λ) (_ : HopfAlgebra R Λ) (_ : Module.Finite R Λ)
      (_ : Module.Projective R Λ) (e : specOver R Λ ≅ H), IsMonHom e.hom := by
  have : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨⟨Λ⟩, ⟨e⟩⟩ := (essImage_hopfSpec (R := .of R) (G := Grp.mk H)).2 this
  let e' : specOver R Λ ≅ H := (Grp.forget _).mapIso e
  have h₁ : IsFinite (specOver R Λ).hom := by
    rw [← Over.w e'.hom]; infer_instance
  have h₂ : Flat (specOver R Λ).hom := by
    rw [← Over.w e'.hom]; infer_instance
  have : Module.Finite R Λ := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h₁)
  have : Module.Flat R Λ := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h₂)
  have : Module.FinitePresentation R Λ := Module.finitePresentation_of_finite R Λ
  exact ⟨Λ, inferInstance, inferInstance, inferInstance,
    Module.Flat.projective_of_finitePresentation, e', e.hom.hom.isMonHom_hom⟩
end GlobalTheory.AffineQuotient
