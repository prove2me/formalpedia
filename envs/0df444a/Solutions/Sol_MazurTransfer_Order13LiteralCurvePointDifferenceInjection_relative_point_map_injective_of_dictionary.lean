-- Prove2me | solution 1 for MazurTransfer.Order13LiteralCurvePointDifferenceInjection.relative_point_map_injective_of_dictionary
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T04:04:57.841973+00:00
-- url     : https://prove2.me/submissions/4d2052b0-2271-44a3-852f-6013869a9b1c

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the genuine point-difference dictionary on the literal
geometric field curve forces injectivity of its map to an original-base
Picard scheme. Named downstream consumer: the integral Abel-Jacobi map
and injectivity of rational curve specialization. -/
import Theorems.Thm_MazurTransfer_CurveModelPointDifferenceInjectivity_point_map_injective_of_dictionary
import Definitions.Def_MazurTransfer_Order13ActualCurveModel
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Theorems.Thm_MazurTransfer_Order13ActualCurveBaseChange_wholeCurve_isPullback
import Definitions.Def_MazurTransfer_Order13IntegralInfinitySections
import Definitions.Def_MazurTransfer_PullbackRelativeFieldPoints
import Definitions.Def_MazurTransfer_RelativePointPostcomposition
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase





noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections
open Order13ActualCurveBaseChange CurveModelPointDifferenceInjectivity Order13ActualArithmeticCurveModel
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open ProperPointSpecializationNaturality
universe u
variable {R K : Type u} [CommRing R] [Field K] [CharZero K] [IsAlgClosed K] [Algebra R K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

variable (D : RelativePic0Designation R (curveToBase R)) (aj : SchemeHomOver (curveToBase R) D.toBase)

theorem solution
    (H : ∃ pts : Pic0 K (actualCurveFunctionField K) ≃ SchemeHomOver (specMap R K) D.toBase,
      ∀ p : SchemeHomOver (𝟙 (Spec (.of K))) (curveToBase K),
        ∃ E : Divisor.degZero (K := K) (F := actualCurveFunctionField K),
          (E : Divisor K (actualCurveFunctionField K)) =
            Finsupp.single ((actualCurveModel K).pointEquivPlace p) 1 -
              Finsupp.single ((actualCurveModel K).pointEquivPlace (positiveInfinitySection K)) 1 ∧
          (pts (Pic0.mk E)).val = (p.val ≫ curveMap R K) ≫ aj.val) :
    Function.Injective (postcomp (curveToBase R) D.toBase aj.val aj.property (specMap R K)) := by
  obtain ⟨pts,hpts⟩ := H
  let u := PullbackRelativeFieldPoints.project (curveToBase R) (curveToBase K)
    (curveMap R K) (specMap R K) (wholeCurve_isPullback R K)
  let j := fun p : ModelPoint (actualCurveModel K) =>
    postcomp (curveToBase R) D.toBase aj.val aj.property (specMap R K) (u p)
  have hj : Function.Injective j := by
    apply point_map_injective_of_dictionary (actualCurveModel K)
      (actual_constantsAreBase_good_characteristic K)
      (by rw [actual_genusFF_eq_two_good_characteristic]; decide) pts j (positiveInfinitySection K)
    intro p
    obtain ⟨E,hE,he⟩ := hpts p
    exact ⟨E,hE,Subtype.ext he⟩
  have hu : Function.Surjective u := (PullbackRelativeFieldPoints.project_bijective
    (curveToBase R) (curveToBase K) (curveMap R K) (specMap R K) (wholeCurve_isPullback R K)).2
  intro x y hxy
  obtain ⟨p,rfl⟩ := hu x
  obtain ⟨q,rfl⟩ := hu y
  exact congrArg u (hj hxy)




#print axioms solution
