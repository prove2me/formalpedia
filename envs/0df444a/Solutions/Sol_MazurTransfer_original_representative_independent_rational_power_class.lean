-- Prove2me | solution 1 for MazurTransfer.original_representative_independent_rational_power_class
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T00:10:59.194865+00:00
-- url     : https://prove2.me/submissions/23dfb04d-67b3-4121-aa22-7761aed694ed

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: for the same original submodule and given original root representative family, the rational power-class value is independent of the representative, injective, and preserves zero and addition.
Named downstream consumer: the original rational radicand linear injection of the actual selected pi Selmer subspace.
-/
import Definitions.Def_MazurTransfer_OriginalContinuousRationalRadicandRepresentativeData20261019
import Theorems.Thm_MazurTransfer_original_rational_nineteenth_power_class_equality_and_exponent
import Theorems.Thm_MazurTransfer_original_rational_root_class_comparison
import Theorems.Thm_MazurTransfer_original_rational_root_zero_and_addition
noncomputable section
open MazurTransfer NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousRationalRootClassKernel RationalNineteenthPowerClasses ContinuousCoefficientExponentAndContinuity ContinuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatH1AlgEquivRatCoefficientAdditiveSubtypeUnitsMemSubgroupRootsRootsRepresentation_continuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatAdditivePowerClasses_continuousRationalRadicandMap
namespace MazurTransfer.OriginalRepresentativeIndependentRationalPowerClassBoundary20261019
end MazurTransfer.OriginalRepresentativeIndependentRationalPowerClassBoundary20261019
namespace MazurTransfer.OriginalRepresentativeIndependentRationalPowerClassProof20261019
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
local notation "Γ" => K ≃ₐ[ℚ] K
local notation "M" => Coefficient (rootsRepresentation K)
local notation "H" => H1 Γ M
theorem powerClass_eq_of_representative (W : Submodule (ZMod 19) H)
    (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)) (x : W)
    (c : continuousCocycles Γ M) (a : ℚˣ) (β : K)
    (hc : classMap Γ M c = x.val) (hroot : RepresentsRoot K c a β) :
    classOf a = powerClass K W hrep x := by
  apply (MazurTransfer.original_rational_nineteenth_power_class_equality_and_exponent.1 _ _).mpr
  apply (MazurTransfer.original_rational_root_class_comparison.2 K c (representative K W hrep x).cocycle
    a (representative K W hrep x).radicand β (representative K W hrep x).root
    hroot (representative K W hrep x).root_spec).mp
  exact hc.trans (representative K W hrep x).class_eq.symm
theorem powerClass_injective (W : Submodule (ZMod 19) H)
    (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)) : Function.Injective (powerClass K W hrep) := by
  intro x y h
  have hr := (MazurTransfer.original_rational_nineteenth_power_class_equality_and_exponent.1 _ _).mp h
  have hc := (MazurTransfer.original_rational_root_class_comparison.2 K
    (representative K W hrep x).cocycle (representative K W hrep y).cocycle
    (representative K W hrep x).radicand (representative K W hrep y).radicand
    (representative K W hrep x).root (representative K W hrep y).root
    (representative K W hrep x).root_spec (representative K W hrep y).root_spec).mpr hr
  exact Subtype.ext ((representative K W hrep x).class_eq.symm.trans
    (hc.trans (representative K W hrep y).class_eq))
theorem powerClass_zero (W : Submodule (ZMod 19) H)
    (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)) : powerClass K W hrep 0 = 1 := by
  have h := powerClass_eq_of_representative K W hrep 0 0 1 1 (map_zero _) (MazurTransfer.original_rational_root_zero_and_addition.1 K)
  exact h.symm.trans (map_one classOf)
theorem powerClass_add (W : Submodule (ZMod 19) H)
    (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)) (x y : W) :
    powerClass K W hrep (x + y) = powerClass K W hrep x * powerClass K W hrep y := by
  let r := representative K W hrep x
  let s := representative K W hrep y
  have hc : classMap Γ M (r.cocycle + s.cocycle) = (x + y).val := by
    exact (map_add (classMap Γ M) r.cocycle s.cocycle).trans
      (congrArg₂ (fun a b : H => a + b) r.class_eq s.class_eq)
  have h := powerClass_eq_of_representative K W hrep (x + y)
    (r.cocycle + s.cocycle) (r.radicand * s.radicand) (r.root * s.root) hc
    (MazurTransfer.original_rational_root_zero_and_addition.2.2 K _ _ _ _ _ _ r.root_spec s.root_spec)
  exact h.symm.trans (map_mul classOf r.radicand s.radicand)
end MazurTransfer.OriginalRepresentativeIndependentRationalPowerClassProof20261019
theorem solution : (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (W : Submodule (ZMod 19) (H1 (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)))) (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)) (x : W) (c : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a : ℚˣ) (β : K) (hc : classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) c = x.val) (hroot : RepresentsRoot K c a β), classOf a = powerClass K W hrep x) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (W : Submodule (ZMod 19) (H1 (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)))) (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)), Function.Injective (powerClass K W hrep)) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (W : Submodule (ZMod 19) (H1 (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)))) (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)), powerClass K W hrep 0 = 1) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (W : Submodule (ZMod 19) (H1 (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)))) (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)) (x y : W), powerClass K W hrep (x + y) = powerClass K W hrep x * powerClass K W hrep y) := by
  exact ⟨MazurTransfer.OriginalRepresentativeIndependentRationalPowerClassProof20261019.powerClass_eq_of_representative, MazurTransfer.OriginalRepresentativeIndependentRationalPowerClassProof20261019.powerClass_injective, MazurTransfer.OriginalRepresentativeIndependentRationalPowerClassProof20261019.powerClass_zero, MazurTransfer.OriginalRepresentativeIndependentRationalPowerClassProof20261019.powerClass_add⟩
#print axioms solution
