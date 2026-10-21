-- Prove2me | solution 1 for MazurTransfer.original_rational_root_inertia_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T23:42:53.571729+00:00
-- url     : https://prove2.me/submissions/46f5ef01-dd9d-4a74-9785-6ae1a90398e6

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: The original represented rational-root class restricts to zero exactly when its same radicand has a nonzero root fixed by the same given subgroup. Every original field, characteristic-zero, subgroup, representation and class hypothesis is retained. Named downstream consumer: genuine valuation inertia divisibility for the original actual pi Selmer radicands.
-/
import Definitions.Def_MazurTransfer_OriginalContinuousRationalRootClassData20261019
import Theorems.Thm_MazurTransfer_original_continuous_rational_root_class_zero_criterion
import Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionWithCoboundaryLawDataV220261018
noncomputable section
open MazurTransfer NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousRationalRootClassKernel
open ContinuousFirstCohomologySubgroupRestriction
attribute [local instance] MazurTransfer.ContinuousRationalRootClassKernel.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRootClassKernel
namespace MazurTransfer.OriginalRationalRootInertiaCriterionBoundary20261019
end MazurTransfer.OriginalRationalRootInertiaCriterionBoundary20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the restriction of the existing represented rational
mu19 class to a given subgroup is zero exactly when the same radicand
has a nonzero root fixed by that subgroup. The coefficient group,
arithmetic action, and H1 restriction are the existing ones.
Named downstream consumer: valuation divisibility for the actual pi
Selmer subspace using its proved inertia restriction conditions.
-/

noncomputable section
namespace MazurTransfer.OriginalRationalRootInertiaCriterionProof20261019
open NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologySubgroupRestriction
open ContinuousRationalRootClassKernel
variable (K : Type) [Field K] [CharZero K]

local notation "Γ" => K ≃ₐ[ℚ] K
local notation "M" => Coefficient (rootsRepresentation K)

theorem exists_fixed_root_of_restriction_zero (S : Subgroup Γ) (z : continuousCocycles Γ M) (a : ℚˣ) (β : K)
    (hroot : RepresentsRoot K z a β)
    (hz : restriction Γ M S (classMap Γ M z) = 0) :
    ∃ α : K, α ≠ 0 ∧ α ^ 19 = algebraMap ℚ K (a : ℚ) ∧
      ∀ σ : S, σ.val α = α := by
  obtain ⟨hβ, hp, hσ⟩ := hroot
  obtain ⟨m, hm⟩ := (restriction_classMap_zero_iff Γ M S z).mp hz
  let γ : K := value K m
  have hγ : γ ≠ 0 := MazurTransfer.original_continuous_rational_root_class_zero_criterion.1 K m
  have hγp : γ ^ 19 = 1 := MazurTransfer.original_continuous_rational_root_class_zero_criterion.2.2.1 K m
  have hγσ (σ : S) : σ.val γ = value K (Additive.toMul (z.val σ.val)) * γ := by
    have h := congrArg (value K) (hm σ)
    change value K ((σ.val • m) / m) = _ at h
    rw [MazurTransfer.original_continuous_rational_root_class_zero_criterion.2.2.2.2.1, MazurTransfer.original_continuous_rational_root_class_zero_criterion.2.2.2.1] at h
    exact (div_eq_iff hγ).mp h
  refine ⟨β / γ, div_ne_zero hβ hγ, ?_, ?_⟩
  · rw [div_pow, hp, hγp, div_one]
  · intro σ
    rw [map_div₀, hσ σ.val, hγσ σ]
    exact mul_div_mul_left β γ (MazurTransfer.original_continuous_rational_root_class_zero_criterion.1 K _)

theorem restriction_zero_of_exists_fixed_root (S : Subgroup Γ) (z : continuousCocycles Γ M) (a : ℚˣ) (β : K)
    (hroot : RepresentsRoot K z a β)
    (ha : ∃ α : K, α ≠ 0 ∧ α ^ 19 = algebraMap ℚ K (a : ℚ) ∧
      ∀ σ : S, σ.val α = α) :
    restriction Γ M S (classMap Γ M z) = 0 := by
  obtain ⟨hβ, hp, hσ⟩ := hroot
  obtain ⟨α, hα, hαp, hαfixed⟩ := ha
  let γ : K := β / α
  have hγ : γ ≠ 0 := div_ne_zero hβ hα
  have hγp : γ ^ 19 = 1 := by
    dsimp [γ]
    rw [div_pow, hp, hαp, div_self ((map_ne_zero (algebraMap ℚ K)).mpr (Units.ne_zero a))]
  let ζ : Roots K := ⟨Units.mk0 γ hγ, Units.ext hγp⟩
  let m : M := ⟨Additive.ofMul ζ⟩
  have hm : value K m = γ := rfl
  apply (restriction_classMap_zero_iff Γ M S z).mpr
  refine ⟨m, fun σ => MazurTransfer.original_continuous_rational_root_class_zero_criterion.2.1 K ?_⟩
  change value K ((σ.val • m) / m) = _
  rw [MazurTransfer.original_continuous_rational_root_class_zero_criterion.2.2.2.2.1, MazurTransfer.original_continuous_rational_root_class_zero_criterion.2.2.2.1, hm]
  change σ.val (β / α) / (β / α) = _
  rw [map_div₀, hαfixed σ, hσ σ.val]
  field_simp

theorem restriction_zero_iff_exists_fixed_root (S : Subgroup Γ) (z : continuousCocycles Γ M) (a : ℚˣ) (β : K)
    (hroot : RepresentsRoot K z a β) :
    restriction Γ M S (classMap Γ M z) = 0 ↔
    ∃ α : K, α ≠ 0 ∧ α ^ 19 = algebraMap ℚ K (a : ℚ) ∧
      ∀ σ : S, σ.val α = α :=
  ⟨exists_fixed_root_of_restriction_zero K S z a β hroot,
    restriction_zero_of_exists_fixed_root K S z a β hroot⟩

end MazurTransfer.OriginalRationalRootInertiaCriterionProof20261019

theorem solution : (∀ (K : Type) [Field K] [CharZero K] (S : Subgroup (K ≃ₐ[ℚ] K)) (z : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a : ℚˣ) (β : K) (hroot : RepresentsRoot K z a β) (hz : restriction (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) S (classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) z) = 0), ∃ α : K, α ≠ 0 ∧ α ^ 19 = algebraMap ℚ K (a : ℚ) ∧ ∀ σ : S, σ.val α = α) ∧ (∀ (K : Type) [Field K] [CharZero K] (S : Subgroup (K ≃ₐ[ℚ] K)) (z : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a : ℚˣ) (β : K) (hroot : RepresentsRoot K z a β) (ha : ∃ α : K, α ≠ 0 ∧ α ^ 19 = algebraMap ℚ K (a : ℚ) ∧ ∀ σ : S, σ.val α = α), restriction (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) S (classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) z) = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] (S : Subgroup (K ≃ₐ[ℚ] K)) (z : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a : ℚˣ) (β : K) (hroot : RepresentsRoot K z a β), restriction (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) S (classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) z) = 0 ↔ ∃ α : K, α ≠ 0 ∧ α ^ 19 = algebraMap ℚ K (a : ℚ) ∧ ∀ σ : S, σ.val α = α) := by
  exact ⟨MazurTransfer.OriginalRationalRootInertiaCriterionProof20261019.exists_fixed_root_of_restriction_zero, MazurTransfer.OriginalRationalRootInertiaCriterionProof20261019.restriction_zero_of_exists_fixed_root, MazurTransfer.OriginalRationalRootInertiaCriterionProof20261019.restriction_zero_iff_exists_fixed_root⟩
#print axioms solution
