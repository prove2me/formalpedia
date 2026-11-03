-- Prove2me | solution 1 for MazurTransfer.original_actual_nineteen_norm_torsor_models
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-11-02T19:19:17.634032+00:00
-- url     : https://prove2.me/submissions/5973d77c-a710-45c4-9e63-f10e87f447be

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: both actual nineteen norm torsors use the same canonical unique integral extension of each original rational Picard point, together with the coherent normalized selected pi quotient.
Named downstream consumer: actual literal mu19 torsor-cocycle pushforward and the nineteen Kummer unit condition.
-/
import Definitions.Def_MazurTransfer_OriginalActualNineteenNormTorsorModelsData20261020
import Theorems.Thm_MazurTransfer_original_actual_pi_mu19_coherent_quotient
import Theorems.Thm_MazurTransfer_original_actual_integral_norm_preimage_torsors
import Theorems.Thm_MazurTransfer_original_nineteen_integral_point_compatibility
noncomputable section
open MazurTransfer

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13LocalIntegralCoefficientMaps Order13ExceptionalNineteenFlatNormFibres
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardNormKummerCocycles Order13NineteenIntegralPointCompatibility
open Order13ActualIntegralNormPreimageTorsors Order13ActualPiMu19CoherentQuotient
open MazurTorsion.XOneThirteenProjectiveCurve
open scoped CategoryTheory.MonObj
open MazurTransfer.Order13ActualNineteenNormTorsorModels
local notation "R" => LocalRing 19
local notation "F" => AlgebraicClosure ℚ
attribute [local instance] MazurTransfer.Order13ActualNineteenNormTorsorModels.instFactPrimeOfNatNat_order13ActualNineteenNormTorsorModels
attribute [local instance] MazurTransfer.Order13ActualNineteenNormTorsorModels.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualNineteenNormTorsorModels
attribute [local instance] MazurTransfer.Order13ActualNineteenNormTorsorModels.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualNineteenNormTorsorModels
attribute [local instance] MazurTransfer.Order13ActualNineteenNormTorsorModels.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNineteenNormTorsorModels
namespace MazurTransfer.OriginalActualNineteenNormTorsorModelsBoundary20261020
end MazurTransfer.OriginalActualNineteenNormTorsorModelsBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: BOTH actual nineteen norm torsors use the SAME canonical
unique integral extension of EACH previously defined rational Picard point.
Retain the coherent normalized selected-pi kernel quotient alongside them.
Named downstream consumer: actual mu19 torsor-cocycle pushforward and the
nineteen unit Kummer condition; a unit condition is not asserted here.
-/

noncomputable section
namespace MazurTransfer.OriginalActualNineteenNormTorsorModelsProof20261020
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13LocalIntegralCoefficientMaps Order13ExceptionalNineteenFlatNormFibres
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardNormKummerCocycles Order13NineteenIntegralPointCompatibility
open Order13ActualIntegralNormPreimageTorsors Order13ActualPiMu19CoherentQuotient
open MazurTorsion.XOneThirteenProjectiveCurve
open scoped CategoryTheory.MonObj





variable (a : RationalPoints)



theorem actual_both_canonical_nineteen_norm_torsors : HasCanonicalActualNineteenNormTorsors a := by
  have h := MazurTransfer.original_actual_integral_norm_preimage_torsors 19 nineteen_good
    (integralPoint (overHomToSchemeHomOver a))
  exact ⟨MazurTransfer.original_nineteen_integral_point_compatibility.1 (overHomToSchemeHomOver a),
    fun b hb => MazurTransfer.original_nineteen_integral_point_compatibility.2.1 (overHomToSchemeHomOver a) b hb, h.1, h.2⟩

theorem actual_coherent_mu19_kernel_and_all_nineteen_norm_torsors
    (z : F) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) :
    HasCoherentActualPiMu19Model z hz 𝒱 ∧ ∀ a : RationalPoints, HasCanonicalActualNineteenNormTorsors a :=
  ⟨MazurTransfer.original_actual_pi_mu19_coherent_quotient z hz 𝒱, actual_both_canonical_nineteen_norm_torsors⟩

end MazurTransfer.OriginalActualNineteenNormTorsorModelsProof20261020

theorem solution : (∀ (a : RationalPoints), HasCanonicalActualNineteenNormTorsors a) ∧ (∀ (z : F) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover),
HasCoherentActualPiMu19Model z hz 𝒱 ∧ ∀ a : RationalPoints, HasCanonicalActualNineteenNormTorsors a) := by
  exact ⟨MazurTransfer.OriginalActualNineteenNormTorsorModelsProof20261020.actual_both_canonical_nineteen_norm_torsors, MazurTransfer.OriginalActualNineteenNormTorsorModelsProof20261020.actual_coherent_mu19_kernel_and_all_nineteen_norm_torsors⟩
#print axioms solution
