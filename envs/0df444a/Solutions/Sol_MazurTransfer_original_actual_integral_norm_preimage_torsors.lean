-- Prove2me | solution 1 for MazurTransfer.original_actual_integral_norm_preimage_torsors
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-11-02T17:10:57.778325+00:00
-- url     : https://prove2.me/submissions/c034105d-ce24-4900-ab33-f6b6b4cbee35

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: both same actual integral norm maps have their finite flat preimage torsors at every good prime and every local section, retaining the original action on all scheme points.
Named downstream consumer: the selected literal mu19 pi quotient torsor and its Kummer unit condition.
-/
import Definitions.Def_MazurTransfer_OriginalActualIntegralNormPreimageTorsorsData20261020
import Theorems.Thm_MazurTransfer_original_integral_norms_finite_flat_all_good_primes
import Theorems.Thm_MazurTransfer_original_relative_finite_flat_norm_preimage_torsor
noncomputable section
open MazurTransfer

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions Order13GoodPrimeIntegralNormGroupLaws
open Order13GoodPrimeIntegralNormPointwiseUnit
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open RelativeFiniteFlatNormPreimageTorsor
open scoped CategoryTheory.MonObj
open MazurTransfer.Order13ActualIntegralNormPreimageTorsors
attribute [local instance] MazurTransfer.Order13ActualIntegralNormPreimageTorsors.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualIntegralNormPreimageTorsors
attribute [local instance] MazurTransfer.Order13ActualIntegralNormPreimageTorsors.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualIntegralNormPreimageTorsors
attribute [local instance] MazurTransfer.Order13ActualIntegralNormPreimageTorsors.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralNormPreimageTorsors
namespace MazurTransfer.OriginalActualIntegralNormPreimageTorsorsBoundary20261020
end MazurTransfer.OriginalActualIntegralNormPreimageTorsorsBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: BOTH SAME actual integral norm extensions have actual
finite-flat fppf preimage torsors of EVERY given local Picard section.
Retain the principal-action isomorphism on ALL scheme-valued points.
Named downstream consumer: the selected normalized mu19 pi quotient's
unit Kummer condition at nineteen, and inverse-character twisted descent.
-/

noncomputable section
namespace MazurTransfer.OriginalActualIntegralNormPreimageTorsorsProof20261020
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions Order13GoodPrimeIntegralNormGroupLaws
open Order13GoodPrimeIntegralNormPointwiseUnit
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open RelativeFiniteFlatNormPreimageTorsor
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)

variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
variable (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of (LocalRing q)))) (localPicard q hq).toBase)






include hq in
theorem actual_both_integral_norm_preimage_torsors :
    HasIntegralNormPreimageTorsor q hq schemePi a ∧
      HasIntegralNormPreimageTorsor q hq schemePiConjugate a := by
  have h := MazurTransfer.original_integral_norms_finite_flat_all_good_primes.1 q hq
  letI : IsFinite (integralPi q hq).val := h.1.1
  letI : Flat (integralPi q hq).val := h.1.2.1
  letI : LocallyOfFinitePresentation (integralPi q hq).val := h.1.2.2.1
  letI : Surjective (integralPi q hq).val := h.1.2.2.2
  letI : IsFinite (integralPiConjugate q hq).val := h.2.1
  letI : Flat (integralPiConjugate q hq).val := h.2.2.1
  letI : LocallyOfFinitePresentation (integralPiConjugate q hq).val := h.2.2.2.1
  letI : Surjective (integralPiConjugate q hq).val := h.2.2.2.2
  exact ⟨MazurTransfer.original_relative_finite_flat_norm_preimage_torsor (localLaw q hq) (integralPi q hq)
      (fun t => MazurTransfer.original_integral_norm_unit_and_all_point_identities.2.2 q hq schemePi t)
      (fun t x y => MazurTransfer.original_integral_norm_multiplication q hq schemePi t x y) a,
    MazurTransfer.original_relative_finite_flat_norm_preimage_torsor (localLaw q hq) (integralPiConjugate q hq)
      (fun t => MazurTransfer.original_integral_norm_unit_and_all_point_identities.2.2 q hq schemePiConjugate t)
      (fun t x y => MazurTransfer.original_integral_norm_multiplication q hq schemePiConjugate t x y) a⟩

end MazurTransfer.OriginalActualIntegralNormPreimageTorsorsProof20261020

theorem solution : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of (LocalRing q)))) (localPicard q hq).toBase),
HasIntegralNormPreimageTorsor q hq schemePi a ∧
      HasIntegralNormPreimageTorsor q hq schemePiConjugate a) := by
  exact MazurTransfer.OriginalActualIntegralNormPreimageTorsorsProof20261020.actual_both_integral_norm_preimage_torsors
#print axioms solution
