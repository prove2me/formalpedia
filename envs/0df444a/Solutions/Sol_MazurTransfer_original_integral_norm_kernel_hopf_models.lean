-- Prove2me | solution 1 for MazurTransfer.original_integral_norm_kernel_hopf_models
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T06:26:28.505756+00:00
-- url     : https://prove2.me/submissions/9d7e896a-a9aa-4168-bcc2-18458452ccb5

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete finite-flat Hopf representation inputs reuse official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: finite-free cocommutative integral Hopf models of the kernels of both same selected integral norms, with their original local-law multiplication and all algebra base-change maps, including at nineteen.
Named downstream consumer: actual arithmetic kernel Hopf labels and finite-flat ordered character quotients at nineteen.
-/
import Definitions.Def_MazurTransfer_OriginalExceptionalNineteenNormModelData20261020
import Definitions.Def_MazurTransfer_OriginalRelativeNormKernelSchemePointsAndGroupLawData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePi_isMonHom
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePiConjugate_isMonHom
import Theorems.Thm_MazurTransfer_original_relative_norm_kernel_hopf_representability
import Theorems.Thm_MazurTransfer_original_local_picard_group_law_commutative
import Theorems.Thm_MazurTransfer_original_integral_norms_finite_flat_all_good_primes
import Theorems.Thm_MazurTransfer_original_integral_norm_unit_and_all_point_identities
import Theorems.Thm_MazurTransfer_original_integral_norm_multiplication
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13GoodPrimeLocalPicardModels MazurTransfer.Order13GoodPrimeIntegralNormExtensions
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm MazurTransfer.Order13ActualPicardSchemeNormGroupHom
open MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf
open MazurTransfer.Order13ExceptionalNineteenFlatNormFibres
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup
attribute [local instance] MazurTransfer.Order13ActualPicardSchemeNormGroupHom.schemePi_isMonHom
attribute [local instance] MazurTransfer.Order13ActualPicardSchemeNormGroupHom.schemePiConjugate_isMonHom
attribute [local instance] MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.instFactPrimeOfNatNat_order13ExceptionalNineteenFlatNormFibres
namespace MazurTransfer.OriginalIntegralNormKernelHopfModelsBoundary20261020
end MazurTransfer.OriginalIntegralNormKernelHopfModelsBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finite-free cocommutative Hopf models of the kernels
of BOTH SAME selected integral norm maps, with the actual local-law
multiplication and all algebra base-change maps. This includes nineteen.
Named downstream consumer: extension of the actual ordered arithmetic
character quotients and their local Kummer torsors at nineteen.
-/

noncomputable section
namespace MazurTransfer.OriginalIntegralNormKernelHopfModelsProof20261020
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions Order13LocalIntegralCoefficientMaps
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardSchemeNineteenNorm
open Order13SameIntegralPicardRationalSchemeComparison
open RelativeGroupLawFiniteFlatKernelHopf
open Order13ExceptionalNineteenFlatNormFibres
open scoped CategoryTheory.MonObj



variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)

theorem actual_integral_norm_kernel_hopf_models :
    HasFiniteFreeKernelHopfModel (localLaw q hq) (integralPi q hq) ∧
      HasFiniteFreeKernelHopfModel (localLaw q hq) (integralPiConjugate q hq) := by
  have h := (MazurTransfer.original_integral_norms_finite_flat_all_good_primes).1 q hq
  letI : IsFinite (integralPi q hq).val := h.1.1
  letI : Flat (integralPi q hq).val := h.1.2.1
  letI : IsFinite (integralPiConjugate q hq).val := h.2.1
  letI : Flat (integralPiConjugate q hq).val := h.2.2.1
  exact ⟨(MazurTransfer.original_relative_norm_kernel_hopf_representability).2.2.2 (localLaw q hq) (integralPi q hq)
      (fun t => (MazurTransfer.original_integral_norm_unit_and_all_point_identities).2.2 q hq schemePi t)
      (fun t x y => MazurTransfer.original_integral_norm_multiplication q hq schemePi t x y)
      (MazurTransfer.original_local_picard_group_law_commutative q hq),
    (MazurTransfer.original_relative_norm_kernel_hopf_representability).2.2.2 (localLaw q hq) (integralPiConjugate q hq)
      (fun t => (MazurTransfer.original_integral_norm_unit_and_all_point_identities).2.2 q hq schemePiConjugate t)
      (fun t x y => MazurTransfer.original_integral_norm_multiplication q hq schemePiConjugate t x y)
      (MazurTransfer.original_local_picard_group_law_commutative q hq)⟩


theorem actual_nineteen_norm_kernel_hopf_models :
    HasFiniteFreeKernelHopfModel (localLaw 19 nineteen_good) (integralPi 19 nineteen_good) ∧
      HasFiniteFreeKernelHopfModel (localLaw 19 nineteen_good)
        (integralPiConjugate 19 nineteen_good) :=
  actual_integral_norm_kernel_hopf_models 19 nineteen_good

end MazurTransfer.OriginalIntegralNormKernelHopfModelsProof20261020

theorem solution : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104),
HasFiniteFreeKernelHopfModel (localLaw q hq) (integralPi q hq) ∧
      HasFiniteFreeKernelHopfModel (localLaw q hq) (integralPiConjugate q hq)) ∧ (HasFiniteFreeKernelHopfModel (localLaw 19 nineteen_good) (integralPi 19 nineteen_good) ∧
      HasFiniteFreeKernelHopfModel (localLaw 19 nineteen_good)
        (integralPiConjugate 19 nineteen_good)) := by
  exact ⟨MazurTransfer.OriginalIntegralNormKernelHopfModelsProof20261020.actual_integral_norm_kernel_hopf_models, MazurTransfer.OriginalIntegralNormKernelHopfModelsProof20261020.actual_nineteen_norm_kernel_hopf_models⟩
#print axioms solution
