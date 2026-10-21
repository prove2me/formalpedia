-- Prove2me | solution 1 for MazurTransfer.original_rational_root_zero_and_addition
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T00:01:31.421833+00:00
-- url     : https://prove2.me/submissions/445b49d6-7a33-4650-9161-5367547fbead

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: zero and sums of the original represented literal mu19 rational-root cocycles have the same explicit original unit and product root witnesses.
Named downstream consumer: the original rational radicand group homomorphism and linear Selmer injection.
-/
import Definitions.Def_MazurTransfer_OriginalContinuousRationalRootClassData20261019
noncomputable section
open MazurTransfer NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousRationalRootClassKernel
attribute [local instance] MazurTransfer.ContinuousRationalRootClassKernel.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRootClassKernel
namespace MazurTransfer.OriginalRationalRootZeroAndAdditionBoundary20261019
end MazurTransfer.OriginalRationalRootZeroAndAdditionBoundary20261019
namespace MazurTransfer.OriginalRationalRootZeroAndAdditionProof20261019
variable (K : Type) [Field K] [CharZero K]
local notation "Γ" => K ≃ₐ[ℚ] K
local notation "M" => Coefficient (rootsRepresentation K)
theorem representsRoot_zero : RepresentsRoot K 0 1 1 := by
  refine ⟨one_ne_zero, ?_, ?_⟩
  · simp
  · intro σ
    change σ 1 = (1 : K) * 1
    simp
theorem value_mul (x y : M) : value K (x * y) = value K x * value K y := rfl
theorem representsRoot_add (z w : continuousCocycles Γ M) (a d : ℚˣ) (β γ : K)
    (hz : RepresentsRoot K z a β) (hw : RepresentsRoot K w d γ) :
    RepresentsRoot K (z + w) (a * d) (β * γ) := by
  obtain ⟨hβ, hp, hσ⟩ := hz
  obtain ⟨hγ, hq, hτ⟩ := hw
  refine ⟨mul_ne_zero hβ hγ, ?_, ?_⟩
  · rw [mul_pow, hp, hq, Units.val_mul, map_mul]
  · intro σ
    change σ (β * γ) = value K
      ((Additive.toMul (z.val σ) : M) * (Additive.toMul (w.val σ) : M)) * (β * γ)
    rw [map_mul, hσ σ, hτ σ, value_mul]
    ring
end MazurTransfer.OriginalRationalRootZeroAndAdditionProof20261019
theorem solution : (∀ (K : Type) [Field K] [CharZero K], RepresentsRoot K 0 1 1) ∧ (∀ (K : Type) [Field K] [CharZero K] (x y : Coefficient (rootsRepresentation K)), value K (x * y) = value K x * value K y) ∧ (∀ (K : Type) [Field K] [CharZero K] (z w : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a d : ℚˣ) (β γ : K) (hz : RepresentsRoot K z a β) (hw : RepresentsRoot K w d γ), RepresentsRoot K (z + w) (a * d) (β * γ)) := by
  exact ⟨MazurTransfer.OriginalRationalRootZeroAndAdditionProof20261019.representsRoot_zero, MazurTransfer.OriginalRationalRootZeroAndAdditionProof20261019.value_mul, MazurTransfer.OriginalRationalRootZeroAndAdditionProof20261019.representsRoot_add⟩
#print axioms solution
