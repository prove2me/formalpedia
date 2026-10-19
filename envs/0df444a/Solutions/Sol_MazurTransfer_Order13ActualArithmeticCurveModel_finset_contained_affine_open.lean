-- Prove2me | solution 1 for MazurTransfer.Order13ActualArithmeticCurveModel.finset_contained_affine_open
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T02:53:44.060213+00:00
-- url     : https://prove2.me/submissions/a8c42ebc-5b34-4399-b328-4279f66c2f12

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: every finite set on the actual good-characteristic order13
curve lies in an affine open. Named downstream consumer: the actual CurveModel
used by the integral Abel-Jacobi point-difference injection. This proof uses
the existing public finite-map existence theorem, independent of the explicit
degree-three finite-map construction. Official Anthropic FLT APIs retain
Apache-2.0 and pin 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
import Definitions.Def_MazurTransfer_Order13ActualTwoAffineOpenCover
import Definitions.Def_MazurTransfer_Order13IntegralInfinitySections
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_geometrically_integral
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_finiteMapData_le_isUnit_of_twoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_isAffineOpen_le_preimage_of_finset
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13IntegralSections
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]
theorem solution (F : Finset (curveScheme K)) :
    ∃ U : (curveScheme K).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U := by
  letI : GeometricallyIntegral (curveToBase K) :=
    MazurTransfer.order13_actual_integral_curve_geometrically_integral K
      (isUnit_iff_ne_zero.mpr Fact.out)
  obtain ⟨D,_,_⟩ := SmoothProperCurve.exists_finiteMapData_le_isUnit_of_twoAffineOpenCover
    K (curveToBase K) (positiveInfinitySection K)
    (GoodCharacteristicGeometryPublicProof.MazurTorsion.XOneThirteenProjectiveCurve.actualTwoAffineOpenCover K) 0
  let V : (Spec (CommRingCat.of K)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  obtain ⟨U,hU,_,hF⟩ := D.exists_isAffineOpen_le_preimage_of_finset V F (by
    intro x hx
    trivial)
  exact ⟨U,hU,hF⟩
#print axioms solution
