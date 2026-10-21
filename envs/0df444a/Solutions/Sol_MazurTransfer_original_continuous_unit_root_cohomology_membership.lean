-- Prove2me | solution 1 for MazurTransfer.original_continuous_unit_root_cohomology_membership
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T23:21:05.129235+00:00
-- url     : https://prove2.me/submissions/d6970fc8-90a7-4025-910f-34b805a38da9

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original unit-root submodule of the existing continuous H1 consists exactly of classes with the same original unit-root representatives. No arithmetic finiteness or local-model assertion is assumed.
Named downstream consumer: the actual selected pi Kummer unit condition at nineteen and its original Selmer subspace.
-/
import Definitions.Def_MazurTransfer_OriginalContinuousUnitRootCohomologyData20261019
noncomputable section
open MazurTransfer
open NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousCoefficientExponentAndContinuity ContinuousUnitRootCohomology
attribute [local instance] MazurTransfer.ContinuousUnitRootCohomology.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousUnitRootCohomology
attribute [local instance] MazurTransfer.ContinuousUnitRootCohomology.instModuleZModOfNatNatH1CoefficientAdditiveSubtypeUnitsMemSubgroupRoots_continuousUnitRootCohomology
namespace MazurTransfer.OriginalContinuousUnitRootCohomologyMembershipBoundary20261019
end MazurTransfer.OriginalContinuousUnitRootCohomologyMembershipBoundary20261019
namespace MazurTransfer.OriginalContinuousUnitRootCohomologyMembershipProof20261019
variable (R K Γ : Type) [CommRing R] [Field K] [CharZero K] [Algebra R K] [Group Γ] [TopologicalSpace Γ]
variable (τ : Representation (ZMod 19) Γ (Additive (Roots K))) (ι : Γ →* (K ≃ₐ[ℚ] K))
theorem mem_unitCondition (x : H1 Γ (Coefficient τ)) : x ∈ unitCondition R K Γ τ ι ↔
    ∃ z : continuousCocycles Γ (Coefficient τ), HasUnitRoot R K Γ τ ι z ∧
      classMap Γ (Coefficient τ) z = x := Iff.rfl
theorem classMap_mem_unitCondition (z : continuousCocycles Γ (Coefficient τ))
    (hz : HasUnitRoot R K Γ τ ι z) :
    classMap Γ (Coefficient τ) z ∈ unitCondition R K Γ τ ι := ⟨z, hz, rfl⟩
end MazurTransfer.OriginalContinuousUnitRootCohomologyMembershipProof20261019
theorem solution : (∀ (R K Γ : Type) [CommRing R] [Field K] [CharZero K] [Algebra R K] [Group Γ] [TopologicalSpace Γ] (τ : Representation (ZMod 19) Γ (Additive (Roots K))) (ι : Γ →* (K ≃ₐ[ℚ] K)) (x : H1 Γ (Coefficient τ)), x ∈ unitCondition R K Γ τ ι ↔ ∃ z : continuousCocycles Γ (Coefficient τ), HasUnitRoot R K Γ τ ι z ∧ classMap Γ (Coefficient τ) z = x) ∧ (∀ (R K Γ : Type) [CommRing R] [Field K] [CharZero K] [Algebra R K] [Group Γ] [TopologicalSpace Γ] (τ : Representation (ZMod 19) Γ (Additive (Roots K))) (ι : Γ →* (K ≃ₐ[ℚ] K)) (z : continuousCocycles Γ (Coefficient τ)) (hz : HasUnitRoot R K Γ τ ι z), classMap Γ (Coefficient τ) z ∈ unitCondition R K Γ τ ι) := by
  exact ⟨MazurTransfer.OriginalContinuousUnitRootCohomologyMembershipProof20261019.mem_unitCondition, MazurTransfer.OriginalContinuousUnitRootCohomologyMembershipProof20261019.classMap_mem_unitCondition⟩
#print axioms solution
