-- Prove2me | solution 1 for MazurTransfer.Order13SingleSectionFiniteAlgebra.ordinary_reciprocal_glue_base
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T06:15:03.057273+00:00
-- url     : https://prove2.me/submissions/72791226-acc8-447f-86ae-ca77d4ef6329

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual ordinary and reciprocal chart maps agree on their literal ordinary overlap source.
Named downstream consumer: actual inverse finite-chart gluing compatibility. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13CanonicalFiniteMapPrimitiveScopes
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
namespace OrdinaryReciprocalGlueBasePublicProof20261017
variable (K : Type u) [CommRing K]
theorem ordinary_reciprocal_glue :
    Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K))) ≫
      ordinaryChartMap K =
    Spec.map (CommRingCat.ofHom (reciprocalToOrdinary K).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))) ≫
        reciprocalChartMap K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  have hor : (Chart.ordinary : Chart.{u}) ≠ Chart.reciprocal := by intro h; cases h
  have hro : (Chart.reciprocal : Chart.{u}) ≠ Chart.ordinary := hor.symm
  have H := Scheme.GlueData.glue_condition (glueData K) Chart.ordinary Chart.reciprocal
  dsimp [glueData, categoricalGlueData, CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f', ordinaryChartMap, reciprocalChartMap] at H
  simp only [dif_neg hor, dif_neg hro, Category.assoc,
    CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl, Category.id_comp] at H
  rw [CategoryTheory.cancel_epi] at H
  exact H.symm
end OrdinaryReciprocalGlueBasePublicProof20261017
open MazurTransfer

theorem solution (R : Type u) [CommRing R] :
    Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R))) ≫
      ordinaryChartMap R =
    Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase R).toRingHom) ≫ reciprocalChartMap R := by
  have he : Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase R).toRingHom) =
      Spec.map (CommRingCat.ofHom (reciprocalToOrdinary R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R) (ReciprocalOverlapRing R))) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (reciprocalToOrdinary_algebraMap R a).symm
  rw [he,Category.assoc]
  exact OrdinaryReciprocalGlueBasePublicProof20261017.ordinary_reciprocal_glue R
#print axioms solution
