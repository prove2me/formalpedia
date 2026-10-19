-- Prove2me | solution 1 for MazurTransfer.Order13ActualInfinityPlaceCenters.localEmbedding_eq_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T13:05:23.25917+00:00
-- url     : https://prove2.me/submissions/98e94132-f04b-4885-a881-58450f73a892

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the two reciprocal-localization places with the
canonical places centered at the two literal rational infinity sections.
Named downstream consumer: the actual degree-19 Pell principal divisor.
The actual stalk diagram supplies the identification, rather than a supplied
valuation equivalence or a substituted abstract curve.
-/
import Definitions.Def_MazurTransfer_Order13ActualInfinityPlaceCenterData
import Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldStalk_local_stalk_coordinate_commutes
noncomputable section
open MazurTransfer AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityLocalParameter Order13ReciprocalChartActualFunctionField Order13ActualInfinityPlaceCenters
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
theorem solution (a : ℚ) (ha : a ^ 2 = 1) :
    localEmbedding ℚ a ha =
      (algebraMap ((curveScheme ℚ).presheaf.stalk (center a ha)) (actualCurveFunctionField ℚ)).comp
        (localStalkIso a ha).hom.hom := by
  apply IsLocalization.ringHom_ext (infinityIdeal ℚ a ha).primeCompl
  have H := AffineOpenChartFunctionFieldStalk.local_stalk_coordinate_commutes
    (.of (ReciprocalRing ℚ)) (reciprocalChartMap ℚ) (chartPoint a ha)
  apply RingHom.ext
  intro b
  rw [RingHom.comp_apply, localEmbedding_coordinate]
  exact congrArg (fun f => f.hom b) H


#print axioms solution
