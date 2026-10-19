-- Prove2me | solution 1 for MazurTransfer.Order13ChartOverlapFunctionField.ordinary_embedding_overlap
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T13:41:32.669283+00:00
-- url     : https://prove2.me/submissions/557f6ba5-85cb-4041-aa46-39346469048b

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal gluing transition identifies the two affine
coordinate embeddings in the actual scheme function field. Named downstream
consumer: the ordinary-chart expression for the Pell function.
-/
import Definitions.Def_MazurTransfer_Order13ChartOverlapEmbeddingData
import Theorems.Thm_MazurTransfer_Order13ChartOverlapFunctionField_overlap_chart_maps_agree
import Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldNaturality_coordinate_embedding_restriction
noncomputable section
universe u
open MazurTransfer
open Order13ChartOverlapFunctionField
open AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open AffineOpenChartFunctionField AffineOpenChartFunctionFieldNaturality
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩

namespace MazurTransfer.OrdinaryCoordinateEmbeddingOverlapHelpers20261017
variable (A : CommRingCat.{u}) [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec A ⟶ X) [IsOpenImmersion j]

variable (B : CommRingCat.{u}) [IsDomain B] (φ : A ⟶ B)
    [IsOpenImmersion (Spec.map φ)]

theorem coordinate_embedding_restriction_of_eq
    (k : Spec B ⟶ X) [IsOpenImmersion k] (hk : Spec.map φ ≫ j = k) :
    CommRingCat.ofHom (coordinateEmbedding A j) =
      φ ≫ CommRingCat.ofHom (coordinateEmbedding B k) := by
  subst k
  exact coordinate_embedding_restriction A j B φ

end MazurTransfer.OrdinaryCoordinateEmbeddingOverlapHelpers20261017
open MazurTransfer.OrdinaryCoordinateEmbeddingOverlapHelpers20261017
theorem solution (b : CoordinateRing K) :
    algebraMap (CoordinateRing K) (actualCurveFunctionField K) b =
      overlapEmbedding K (ordinaryToReciprocalBase K b) := by
  exact congrArg (fun f => f.hom b)
    (coordinate_embedding_restriction_of_eq (.of (CoordinateRing K)) (ordinaryChartMap K)
      (.of (ReciprocalOverlapRing K)) (CommRingCat.ofHom (ordinaryToReciprocalBase K).toRingHom)
      (Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))) ≫
        reciprocalChartMap K) (overlap_chart_maps_agree K))


#print axioms solution
