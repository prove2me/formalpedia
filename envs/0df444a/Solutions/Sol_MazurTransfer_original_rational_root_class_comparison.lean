-- Prove2me | solution 1 for MazurTransfer.original_rational_root_class_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T23:53:25.852989+00:00
-- url     : https://prove2.me/submissions/b7d9d8f5-f0c3-4c38-b955-05a5e0c87f0c

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: For the same two explicitly represented rational-root classes in the original literal mu19 continuous H1, equality is equivalent to the same rational radicand ratio being a nineteenth power. Their difference has the original quotient root as representative. All original field, characteristic-zero, Galois and representative hypotheses are retained. Named downstream consumer: the original rational radicand linear injection of the actual selected pi Selmer space.
-/
import Definitions.Def_MazurTransfer_OriginalContinuousRationalRootClassData20261019
import Theorems.Thm_MazurTransfer_original_continuous_rational_root_class_zero_criterion
noncomputable section
open MazurTransfer NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousRationalRootClassKernel
attribute [local instance] MazurTransfer.ContinuousRationalRootClassKernel.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRootClassKernel
namespace MazurTransfer.OriginalRationalRootClassComparisonBoundary20261019
end MazurTransfer.OriginalRationalRootClassComparisonBoundary20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: compare explicitly represented classes in the existing
continuous H1 via the nineteenth-power class of their rational radicand
ratio. No arbitrary choice of a Kummer representative is asserted.
Named downstream consumer: injection of the actual selected pi Kummer
image into a rational power-class Selmer group.
-/

noncomputable section
namespace MazurTransfer.OriginalRationalRootClassComparisonProof20261019
open NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients
open ContinuousFirstCohomologyPresentation ContinuousRationalRootClassKernel
variable (K : Type) [Field K] [CharZero K]

local notation "Γ" => K ≃ₐ[ℚ] K
local notation "M" => Coefficient (rootsRepresentation K)

theorem representsRoot_sub (z w : continuousCocycles Γ M) (a d : ℚˣ) (β γ : K)
    (hz : RepresentsRoot K z a β) (hw : RepresentsRoot K w d γ) :
    RepresentsRoot K (z - w) (a / d) (β / γ) := by
  obtain ⟨hβ, hp, hσ⟩ := hz
  obtain ⟨hγ, hq, hτ⟩ := hw
  refine ⟨div_ne_zero hβ hγ, ?_, ?_⟩
  · rw [div_pow, hp, hq, Units.val_div_eq_div_val, map_div₀]
  · intro σ
    change σ (β / γ) = value K
      ((Additive.toMul (z.val σ) : M) / (Additive.toMul (w.val σ) : M)) * (β / γ)
    rw [map_div₀, hσ σ, hτ σ, MazurTransfer.original_continuous_rational_root_class_zero_criterion.2.2.2.2.1, div_mul_div_comm]

variable [IsGalois ℚ K]

theorem classMap_eq_iff_rational_power_ratio (z w : continuousCocycles Γ M) (a d : ℚˣ) (β γ : K)
    (hz : RepresentsRoot K z a β) (hw : RepresentsRoot K w d γ) :
    classMap Γ M z = classMap Γ M w ↔ ∃ b : ℚˣ, b ^ 19 = a / d := by
  have h := MazurTransfer.original_continuous_rational_root_class_zero_criterion.2.2.2.2.2.2.2 K (z - w) (a / d) (β / γ)
    (representsRoot_sub K z w a d β γ hz hw)
  rwa [map_sub, sub_eq_zero] at h

end MazurTransfer.OriginalRationalRootClassComparisonProof20261019

theorem solution : (∀ (K : Type) [Field K] [CharZero K] (z w : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a d : ℚˣ) (β γ : K) (hz : RepresentsRoot K z a β) (hw : RepresentsRoot K w d γ), RepresentsRoot K (z - w) (a / d) (β / γ)) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z w : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a d : ℚˣ) (β γ : K) (hz : RepresentsRoot K z a β) (hw : RepresentsRoot K w d γ), classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) z = classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) w ↔ ∃ b : ℚˣ, b ^ 19 = a / d) := by
  exact ⟨MazurTransfer.OriginalRationalRootClassComparisonProof20261019.representsRoot_sub, MazurTransfer.OriginalRationalRootClassComparisonProof20261019.classMap_eq_iff_rational_power_ratio⟩
#print axioms solution
