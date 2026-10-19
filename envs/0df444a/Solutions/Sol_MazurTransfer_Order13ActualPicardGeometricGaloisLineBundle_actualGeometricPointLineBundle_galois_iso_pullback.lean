-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGeometricGaloisLineBundle.actualGeometricPointLineBundle_galois_iso_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T13:40:17.144084+00:00
-- url     : https://prove2.me/submissions/b08230db-21f7-4d1c-8850-419241c35517

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: the existing actual Picard precomposition Galois action
pulls its actual geometric line bundle along the literal curve Galois
isomorphism. No chosen auxiliary isomorphism equality is asserted.
Named downstream consumer: actual geometric divisor-class Galois naturality. -/
import Definitions.Def_MazurTransfer_Order13ActualGeometricCurveGaloisAutomorphismOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondLineBundleData
import Definitions.Def_MazurTransfer_Order13ActualGeometricNineteenTorsionNaturalDivisorMapOriginalFieldContextDataV320261018
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
noncomputable section
universe u
namespace MazurTransfer.ActualGeometricGaloisLineBundleProofHelpers20261018
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTransfer.PicardCurvePullbackGeometricFieldLineBundle
variable {R : Type u} [CommRing R] {K : Type u} [Field K]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{u}} (j : X ⟶ pullback c t)

theorem originalPoincarePreCompIsoExists20261018 (a : SchemeHomOver t D.toBase) (s : SchemeHomOver t t) :
    Nonempty ((h.poincare.pullbackAlong (postComp a s)).L ≅
      (Scheme.Modules.pullback (baseChangeSnd c s)).obj (h.poincare.pullbackAlong a).L) := by
  exact ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_comp c a s).symm).app h.poincare.L ≪≫
    ((Scheme.Modules.pullbackComp (baseChangeSnd c s) (baseChangeSnd c a)).app h.poincare.L).symm⟩

theorem geometricPointLineBundle_preComp_iso_pullback
    (a : SchemeHomOver t D.toBase) (s : SchemeHomOver t t)
    (g : X ⟶ X) (hcomp : j ≫ baseChangeSnd c s = g ≫ j) :
    Nonempty (geometricPointLineBundle c ε D h t j (postComp a s) ≅
      (Scheme.Modules.pullback g).obj (geometricPointLineBundle c ε D h t j a)) := by
  obtain ⟨i⟩ := originalPoincarePreCompIsoExists20261018 c ε D h t a s
  exact ⟨(Scheme.Modules.pullback j).mapIso i ≪≫
    (Scheme.Modules.pullbackComp j (baseChangeSnd c s)).app (h.poincare.pullbackAlong a).L ≪≫
    (Scheme.Modules.pullbackCongr hcomp).app (h.poincare.pullbackAlong a).L ≪≫
    ((Scheme.Modules.pullbackComp g j).app (h.poincare.pullbackAlong a).L).symm⟩

end MazurTransfer.ActualGeometricGaloisLineBundleProofHelpers20261018
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard MazurTransfer
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGeometricArithmeticGroup
open Order13ActualPicardGeometricDiamondLineBundle Order13GeometricRelativeCurveChange
open Order13ActualGeometricCurveGaloisAutomorphism Order13ActualNormKernelProductCardinality
open ActualGeometricGaloisLineBundleProofHelpers20261018
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018

theorem solution (K : Type) [Field K] [CharZero K] [PerfectField K]
    (σ : K ≃ₐ[ℚ] K) (a : Points K) :
    Nonempty (actualGeometricPointLineBundle K (pointOfOverHom K (actionHom K σ a)) ≅
      (Scheme.Modules.pullback (geometricCurveGaloisIso K σ).hom).obj
        (actualGeometricPointLineBundle K (pointOfOverHom K a))) := by
  let s : SchemeHomOver (FieldAutomorphismOverPointAction.fieldBase ℚ K)
      (FieldAutomorphismOverPointAction.fieldBase ℚ K) :=
    ⟨(fieldSpectrumIso K σ).hom,fieldSpectrumIso_over K σ⟩
  have hp : pointOfOverHom K (actionHom K σ a) = postComp (pointOfOverHom K a) s := by
    apply Subtype.ext
    rfl
  have hj : geometricCurveEmbedding K ≫ baseChangeSnd (curveToBase ℚ) s =
      (geometricCurveGaloisIso K σ).hom ≫ geometricCurveEmbedding K := by
    change geometricCurveEmbedding K ≫ relativeFibreAut K σ = _
    exact (geometricCurveGaloisIso_embedding K σ).symm
  rw [hp]
  exact geometricPointLineBundle_preComp_iso_pullback (curveToBase ℚ) infinitySection
    actualPicard actualRepresentation (FieldAutomorphismOverPointAction.fieldBase ℚ K)
    (geometricCurveEmbedding K) (pointOfOverHom K a) s
    (geometricCurveGaloisIso K σ).hom hj

#print axioms solution
