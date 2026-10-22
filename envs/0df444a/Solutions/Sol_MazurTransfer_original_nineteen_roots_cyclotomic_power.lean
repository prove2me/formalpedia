-- Prove2me | solution 1 for MazurTransfer.original_nineteen_roots_cyclotomic_power
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T18:49:46.996977+00:00
-- url     : https://prove2.me/submissions/f879eeb9-b89e-4777-8245-01a9daa6a207

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same original natural cyclotomic exponent acts on every literal nineteenth root and on the previously fixed roots representation, including the same inverse-character twist on the original character kernel.
Named downstream consumer: cyclotomic Hopf classification of the selected pi quotient and descent of the same conjugate-pi quotient at nineteen.
-/
import Definitions.Def_MazurTransfer_OriginalNineteenRootsCyclotomicPowerData20261020
noncomputable section
open MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.RepresentationCharacterTwist
open MazurTransfer.Order13ActualOrderedCharacterContinuousH1 MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter
open MazurTransfer.NineteenRootsCyclotomicPower
attribute [local instance] MazurTransfer.NineteenRootsCyclotomicPower.instFactPrimeOfNatNat_nineteenRootsCyclotomicPower
attribute [local instance] MazurTransfer.NineteenRootsCyclotomicPower.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_nineteenRootsCyclotomicPower
namespace MazurTransfer.OriginalNineteenRootsCyclotomicPowerBoundary20261020
end MazurTransfer.OriginalNineteenRootsCyclotomicPowerBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME natural exponent acts on every literal nineteenth
root in the field and on the PREVIOUSLY FIXED rootsRepresentation.
The actual inverse-character twist has this action on the character kernel.
Named downstream consumer: cyclotomic Hopf classification of the selected
pi quotient, and descent for the selected conjugate-pi quotient at nineteen.
-/

noncomputable section
namespace MazurTransfer.OriginalNineteenRootsCyclotomicPowerProof20261020
open NineteenRootsGaloisRepresentation RepresentationCharacterTwist
variable (K : Type) [Field K] [CharZero K]





theorem field_root_power (σ : K ≃ₐ[ℚ] K) (ζ : K) (hζ : ζ ^ 19 = 1) :
    σ ζ = ζ ^ exponent K σ := by
  have hne : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hζ
    exact zero_ne_one hζ
  let t : rootsOfUnity 19 K := ⟨Units.mk0 ζ hne, (mem_rootsOfUnity' 19 _).mpr hζ⟩
  exact modularCyclotomicCharacter.toFun_spec σ.toRingEquiv t

theorem roots_representation_nsmul (σ : K ≃ₐ[ℚ] K) (m : Additive (Roots K)) :
    rootsRepresentation K σ m = exponent K σ • m := by
  apply Additive.toMul.injective
  rw [toMul_nsmul]
  apply Subtype.ext
  apply Units.ext
  exact modularCyclotomicCharacter.toFun_spec σ.toRingEquiv m.toMul

theorem nineteen_nsmul (m : Additive (Roots K)) : 19 • m = 0 := by
  apply Additive.toMul.injective
  rw [toMul_nsmul, toMul_zero]
  apply Subtype.ext
  exact m.toMul.property

theorem twisted_representation_on_character_kernel
    (χ : (K ≃ₐ[ℚ] K) →* (ZMod 19)ˣ) (σ : K ≃ₐ[ℚ] K) (hχ : χ σ = 1)
    (m : Additive (Roots K)) :
    twist χ⁻¹ (rootsRepresentation K) σ m = exponent K σ • m := by
  change (((χ σ)⁻¹ : (ZMod 19)ˣ) : ZMod 19) • rootsRepresentation K σ m = _
  rw [hχ, inv_one, Units.val_one, one_smul, roots_representation_nsmul]

variable [IsGalois ℚ K] [IsAlgClosed K]
open Order13ActualOrderedCharacterContinuousH1 Order13ActualCyclotomicThirteenKernelCharacter

theorem actual_twisted_roots_on_character_kernel
    (z : K) (hz : IsPrimitiveRoot z 13) (σ : K ≃ₐ[ℚ] K)
    (hχ : piConjugateReflectedCharacter K z hz σ = 1) (m : Additive (Roots K)) :
    twistedRootsRepresentation K z hz σ m = exponent K σ • m :=
  twisted_representation_on_character_kernel K (piConjugateReflectedCharacter K z hz) σ hχ m

end MazurTransfer.OriginalNineteenRootsCyclotomicPowerProof20261020

theorem solution : (∀ (K : Type) [Field K] [CharZero K] , ∀ (σ : K ≃ₐ[ℚ] K) (ζ : K) (hζ : ζ ^ 19 = 1),
σ ζ = ζ ^ exponent K σ) ∧ (∀ (K : Type) [Field K] [CharZero K] , ∀ (σ : K ≃ₐ[ℚ] K) (m : Additive (Roots K)),
rootsRepresentation K σ m = exponent K σ • m) ∧ (∀ (K : Type) [Field K] [CharZero K] , ∀ (m : Additive (Roots K)),
19 • m = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] , ∀ (χ : (K ≃ₐ[ℚ] K) →* (ZMod 19)ˣ) (σ : K ≃ₐ[ℚ] K) (hχ : χ σ = 1)
    (m : Additive (Roots K)),
twist χ⁻¹ (rootsRepresentation K) σ m = exponent K σ • m) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] , ∀ (z : K) (hz : IsPrimitiveRoot z 13) (σ : K ≃ₐ[ℚ] K)
    (hχ : piConjugateReflectedCharacter K z hz σ = 1) (m : Additive (Roots K)),
twistedRootsRepresentation K z hz σ m = exponent K σ • m) := by
  exact ⟨MazurTransfer.OriginalNineteenRootsCyclotomicPowerProof20261020.field_root_power, MazurTransfer.OriginalNineteenRootsCyclotomicPowerProof20261020.roots_representation_nsmul, MazurTransfer.OriginalNineteenRootsCyclotomicPowerProof20261020.nineteen_nsmul, MazurTransfer.OriginalNineteenRootsCyclotomicPowerProof20261020.twisted_representation_on_character_kernel, MazurTransfer.OriginalNineteenRootsCyclotomicPowerProof20261020.actual_twisted_roots_on_character_kernel⟩
#print axioms solution
