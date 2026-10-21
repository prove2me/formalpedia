-- Prove2me | solution 1 for MazurTransfer.original_continuous_rational_radicand_linear_map_injective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T00:28:23.263008+00:00
-- url     : https://prove2.me/submissions/128a3ce6-9d68-4aa8-8df1-3b72a5dc9cb4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original rational radicand linear map from the same given root-representative family is injective.
Named downstream consumer: the original actual selected pi Selmer power-class support and numerical dimension bound.
-/
import Definitions.Def_MazurTransfer_OriginalContinuousRationalRadicandLinearMapData20261019
noncomputable section
open MazurTransfer NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousRationalRootClassKernel RationalNineteenthPowerClasses ContinuousCoefficientExponentAndContinuity ContinuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatH1AlgEquivRatCoefficientAdditiveSubtypeUnitsMemSubgroupRootsRootsRepresentation_continuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatAdditivePowerClasses_continuousRationalRadicandMap
namespace MazurTransfer.OriginalContinuousRationalRadicandLinearMapInjectivityBoundary20261019
end MazurTransfer.OriginalContinuousRationalRadicandLinearMapInjectivityBoundary20261019
namespace MazurTransfer.OriginalContinuousRationalRadicandLinearMapInjectivityProof20261019
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
local notation "Γ" => K ≃ₐ[ℚ] K
local notation "M" => Coefficient (rootsRepresentation K)
local notation "H" => H1 Γ M
theorem radicandLinearMap_injective (W : Submodule (ZMod 19) H)
    (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)) : Function.Injective (radicandLinearMap K W hrep) := by
  intro x y h
  apply MazurTransfer.original_representative_independent_rational_power_class.2.1 K W hrep
  exact congrArg Additive.toMul h
end MazurTransfer.OriginalContinuousRationalRadicandLinearMapInjectivityProof20261019
theorem solution : ∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (W : Submodule (ZMod 19) (H1 (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)))) (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)), Function.Injective (radicandLinearMap K W hrep) := by
  exact MazurTransfer.OriginalContinuousRationalRadicandLinearMapInjectivityProof20261019.radicandLinearMap_injective
#print axioms solution
