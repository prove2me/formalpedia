-- Prove2me | solution 1 for MazurTransfer.Order13ActualInfinityPlaceCenters.infinityPlace_eq_actualPlaceOfPoint
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T13:15:22.736162+00:00
-- url     : https://prove2.me/submissions/6fded6c3-54a2-4c15-833f-b3ded8af5bb4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the two reciprocal-localization places with the
canonical places centered at the two literal rational infinity sections.
Named downstream consumer: the actual degree-19 Pell principal divisor.
The actual stalk diagram supplies the identification, rather than a supplied
valuation equivalence or a substituted abstract curve.
-/
import Definitions.Def_MazurTransfer_Order13ActualInfinitySectionCenterCertificates
import Theorems.Thm_MazurTransfer_Order13ActualInfinityPlaceCenters_localEmbedding_eq_stalk
noncomputable section
open MazurTransfer AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityLocalParameter Order13ReciprocalChartActualFunctionField
open Order13PellActualInfinityValuations Order13IntegralSections Order13RationalSectionPicardInjection Order13ActualInfinityPlaceCenters
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
namespace MazurTransfer.ActualInfinityPlaceIdentificationHelpers20261017
theorem localEmbedding_range_eq_stalk (a : ℚ) (ha : a ^ 2 = 1) :
    (localEmbedding ℚ a ha).range =
      (algebraMap ((curveScheme ℚ).presheaf.stalk (center a ha)) (actualCurveFunctionField ℚ)).range := by
  rw [localEmbedding_eq_stalk]
  ext f
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨(localStalkIso a ha).hom b, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (localStalkIso a ha).hom).2 b
    exact ⟨c, rfl⟩

end MazurTransfer.ActualInfinityPlaceIdentificationHelpers20261017
open MazurTransfer.ActualInfinityPlaceIdentificationHelpers20261017
theorem solution (a : ℚ) (ha : a ^ 2 = 1) :
    infinityPlace a ha = actualPlaceOfPoint ℚ (sectionClosedPoint ℚ (infinitySection ℚ a ha)) := by
  apply Place.ext
  apply ValuationSubring.toSubring_injective
  rw [← localEmbedding_range_eq_place, localEmbedding_range_eq_stalk,
    ← infinity_section_center, actualPlaceOfPoint_stalk_range]


#print axioms solution
