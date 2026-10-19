-- Prove2me | solution 1 for MazurTransfer.Order13ChartOverlapFunctionField.overlap_chart_maps_agree
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T13:34:25.635933+00:00
-- url     : https://prove2.me/submissions/61882484-89f4-426d-ac42-9487b495a117

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal gluing transition identifies the two affine
coordinate embeddings in the actual scheme function field. Named downstream
consumer: the ordinary-chart expression for the Pell function.
-/
import Definitions.Def_MazurTransfer_Order13ChartOverlapEmbeddingData
import Theorems.Thm_MazurTransfer_GlueDataPrimeOverlapCompatibility_glue_condition
noncomputable section
universe u
open MazurTransfer
open Order13ChartOverlapFunctionField
open AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open AffineOpenChartFunctionField
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩

theorem solution :
    Spec.map (CommRingCat.ofHom (ordinaryToReciprocalBase K).toRingHom) ≫
        ordinaryChartMap K =
      Spec.map (CommRingCat.ofHom
        (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))) ≫ reciprocalChartMap K := by
  rw [ordinaryToReciprocalBase_spec_map]
  have hro : (Chart.reciprocal : Chart.{u}) ≠ Chart.ordinary := by decide
  let : CategoryTheory.Limits.HasMulticoequalizer
      (GlueData.ofGlueData' (categoricalGlueData K)).diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  have H := GlueDataPrimeOverlapCompatibility.glue_condition (categoricalGlueData K)
    Chart.reciprocal Chart.ordinary hro
  exact (Category.assoc _ _ _).trans H


#print axioms solution
