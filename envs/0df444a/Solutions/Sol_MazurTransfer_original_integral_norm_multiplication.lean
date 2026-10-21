-- Prove2me | solution 1 for MazurTransfer.original_integral_norm_multiplication
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T05:39:19.747152+00:00
-- url     : https://prove2.me/submissions/081bf44e-1dd7-4376-8d9e-1c025842b3d3

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same selected integral norm extensions preserve the multiplication of the original local Picard group law on points over arbitrary original test schemes.
Named downstream consumer: same actual integral norm-kernel Hopf group laws and finite-flat arithmetic quotients.
-/
import Definitions.Def_MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeGenericNormGroupLaws_localGenericNorm_preserves_mul
import Theorems.Thm_MazurTransfer_original_relative_group_law_generic_fibre_multiplication_descent
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison
open MazurTransfer.Order13GoodPrimeGenericNormGroupLaws MazurTransfer.Order13GoodPrimeIntegralNormExtensions
open MazurTransfer.Order13GoodPrimeLocalPicardModels MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup
namespace MazurTransfer.OriginalIntegralNormMultiplicationBoundary20261020
end MazurTransfer.OriginalIntegralNormMultiplicationBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME selected integral norm extensions preserve
multiplication on points over arbitrary schemes, by flat generic descent.
Named downstream consumer: local integral norm group homomorphisms and
finite etale norm fibres away from nineteen.
-/

noncomputable section
namespace MazurTransfer.OriginalIntegralNormMultiplicationProof20261020
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalGenericGroupIdentity Order13GoodPrimeLocalGenericPicardComparison
open Order13GoodPrimeGenericNormGroupLaws Order13GoodPrimeIntegralNormExtensions
open Order13GoodPrimeLocalPicardModels
open Order13LocalIntegralCoefficientMaps Order13ActualPicardDiamondSchemeEndomorphism
open Order13SameIntegralPicardRationalSchemeComparison
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)

theorem integralNorm_preserves_mul
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (LocalRing q)))
    (x y : SchemeHomOver t (localPicard q hq).toBase) :
    NeronModelInfra.schemeHomOverComp ((localLaw q hq).mul t x y) (integralNorm q hq φ) =
    (localLaw q hq).mul t
      (NeronModelInfra.schemeHomOverComp x (integralNorm q hq φ))
      (NeronModelInfra.schemeHomOverComp y (integralNorm q hq φ)) := by
  letI := (localPicard_geometry q hq).1
  letI := (localPicard_geometry q hq).2.1
  apply MazurTransfer.original_relative_group_law_generic_fibre_multiplication_descent ℚ
    (localLaw q hq) (localLaw q hq) (integralNorm q hq φ)
  intro S s a b
  rw [integralNorm_restrict]
  exact localGenericNorm_preserves_mul q hq φ s a b

end MazurTransfer.OriginalIntegralNormMultiplicationProof20261020

theorem solution : ∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (LocalRing q)))
    (x y : SchemeHomOver t (localPicard q hq).toBase),
NeronModelInfra.schemeHomOverComp ((localLaw q hq).mul t x y) (integralNorm q hq φ) =
    (localLaw q hq).mul t
      (NeronModelInfra.schemeHomOverComp x (integralNorm q hq φ))
      (NeronModelInfra.schemeHomOverComp y (integralNorm q hq φ)) := by
  exact MazurTransfer.OriginalIntegralNormMultiplicationProof20261020.integralNorm_preserves_mul
#print axioms solution
