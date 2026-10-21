-- Prove2me | solution 1 for MazurTransfer.original_continuous_rational_root_class_zero_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T23:29:04.921212+00:00
-- url     : https://prove2.me/submissions/e4b24601-2055-4018-9290-784fe9f78784

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a class with an explicit original rational-root representative vanishes exactly when that same rational radicand is a nineteenth power. Preserve the original coefficient value and continuous H1, with no global representability assumption.
Named downstream consumer: the original selected pi Selmer rational radicand injection and prime valuation support bound.
-/
import Definitions.Def_MazurTransfer_OriginalContinuousRationalRootClassData20261019
noncomputable section
open MazurTransfer NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousUnitRootCohomology ContinuousRationalRootClassKernel
attribute [local instance] MazurTransfer.ContinuousRationalRootClassKernel.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRootClassKernel
namespace MazurTransfer.OriginalContinuousRationalRootClassZeroCriterionBoundary20261019
end MazurTransfer.OriginalContinuousRationalRootClassZeroCriterionBoundary20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: for the existing literal mu19 coefficient group and
continuous H1 presentation, an explicitly represented rational root
class vanishes exactly when its rational radicand is a nineteenth power.
No finite-extension hypothesis or global Hilbert 90 surjectivity is used.
Named downstream consumer: rational power-class bounds for the actual
selected pi Selmer subspace.
-/

noncomputable section
namespace MazurTransfer.OriginalContinuousRationalRootClassZeroCriterionProof20261019
open NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients
open ContinuousFirstCohomologyPresentation ContinuousUnitRootCohomology
variable (K : Type) [Field K] [CharZero K]

local notation "Γ" => K ≃ₐ[ℚ] K
local notation "M" => Coefficient (rootsRepresentation K)



theorem value_ne_zero (x : M) : value K x ≠ 0 := Units.ne_zero _

theorem value_injective : Function.Injective (value K) := by
  intro x y h
  apply Coefficient.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  exact Units.ext h

theorem value_pow_nineteen (x : M) : value K x ^ 19 = 1 := by
  exact congrArg (fun u : Kˣ => (u : K)) x.val.toMul.property

theorem value_smul (σ : Γ) (x : M) : value K (σ • x) = σ (value K x) := rfl

theorem value_div (x y : M) : value K (x / y) = value K x / value K y := by
  change ((coefficientUnit K Γ (rootsRepresentation K)) (x / y) : K) = _
  rw [map_div, Units.val_div_eq_div_val]
  rfl



variable [IsGalois ℚ K]

theorem rational_power_of_class_zero (z : continuousCocycles Γ M) (a : ℚˣ) (β : K)
    (hroot : RepresentsRoot K z a β) (hz : classMap Γ M z = 0) :
    ∃ b : ℚˣ, b ^ 19 = a := by
  obtain ⟨hβ, hp, hσ⟩ := hroot
  obtain ⟨m, hm⟩ := groupCohomology.isMulCoboundary₁_of_mem_coboundaries₁
    (fun σ : Γ => (Additive.toMul (z.val σ) : M))
    ((classMap_eq_zero_iff Γ M z).mp hz)
  let γ : K := value K m
  have hγ : γ ≠ 0 := value_ne_zero K m
  have hγp : γ ^ 19 = 1 := value_pow_nineteen K m
  have hγσ (σ : Γ) : σ γ = value K (Additive.toMul (z.val σ)) * γ := by
    have h := congrArg (value K) (hm σ)
    rw [value_div, value_smul] at h
    exact (div_eq_iff hγ).mp h
  have hfixed : ∀ σ : Γ, σ (β / γ) = β / γ := by
    intro σ
    rw [map_div₀, hσ σ, hγσ σ]
    exact mul_div_mul_left β γ (value_ne_zero K _)
  obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (β / γ)).mpr hfixed
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, map_zero] at hb
    exact (div_ne_zero hβ hγ) hb.symm
  refine ⟨Units.mk0 b hb0, ?_⟩
  apply Units.ext
  apply (algebraMap ℚ K).injective
  change algebraMap ℚ K (b ^ 19) = algebraMap ℚ K (a : ℚ)
  rw [map_pow, hb, div_pow, hp, hγp, div_one]

theorem class_zero_of_rational_power (z : continuousCocycles Γ M) (a : ℚˣ) (β : K)
    (hroot : RepresentsRoot K z a β) (ha : ∃ b : ℚˣ, b ^ 19 = a) :
    classMap Γ M z = 0 := by
  obtain ⟨hβ, hp, hσ⟩ := hroot
  obtain ⟨b, hb⟩ := ha
  let c : K := algebraMap ℚ K (b : ℚ)
  have hc : c ≠ 0 := (map_ne_zero (algebraMap ℚ K)).mpr (Units.ne_zero b)
  have hcp : c ^ 19 = algebraMap ℚ K (a : ℚ) := by
    change (algebraMap ℚ K (b : ℚ)) ^ 19 = _
    rw [← map_pow]
    exact congrArg (algebraMap ℚ K) (congrArg (fun u : ℚˣ => (u : ℚ)) hb)
  let γ : K := β / c
  have hγ : γ ≠ 0 := div_ne_zero hβ hc
  have hγp : γ ^ 19 = 1 := by
    dsimp [γ]
    rw [div_pow, hp, hcp, div_self ((map_ne_zero (algebraMap ℚ K)).mpr (Units.ne_zero a))]
  let ζ : Roots K := ⟨Units.mk0 γ hγ, Units.ext hγp⟩
  let m : M := ⟨Additive.ofMul ζ⟩
  have hm : value K m = γ := rfl
  have hγσ (σ : Γ) : σ γ / γ = value K (Additive.toMul (z.val σ)) := by
    change σ (β / c) / (β / c) = _
    have hfix : σ c = c := σ.commutes (b : ℚ)
    rw [map_div₀, hfix, hσ σ]
    field_simp
  apply (classMap_eq_zero_iff Γ M z).mpr
  exact (groupCohomology.coboundariesOfIsMulCoboundary₁
    (f := fun σ : Γ => (Additive.toMul (z.val σ) : M))
    ⟨m, fun σ => value_injective K (by rw [value_div, value_smul, hm]; exact hγσ σ)⟩).property

theorem class_zero_iff_rational_power (z : continuousCocycles Γ M) (a : ℚˣ) (β : K)
    (hroot : RepresentsRoot K z a β) :
    classMap Γ M z = 0 ↔ ∃ b : ℚˣ, b ^ 19 = a :=
  ⟨rational_power_of_class_zero K z a β hroot,
    class_zero_of_rational_power K z a β hroot⟩

end MazurTransfer.OriginalContinuousRationalRootClassZeroCriterionProof20261019

theorem solution : (∀ (K : Type) [Field K] [CharZero K] (x : Coefficient (rootsRepresentation K)), value K x ≠ 0) ∧ (∀ (K : Type) [Field K] [CharZero K], Function.Injective (value K)) ∧ (∀ (K : Type) [Field K] [CharZero K] (x : Coefficient (rootsRepresentation K)), value K x ^ 19 = 1) ∧ (∀ (K : Type) [Field K] [CharZero K] (σ : (K ≃ₐ[ℚ] K)) (x : Coefficient (rootsRepresentation K)), value K (σ • x) = σ (value K x)) ∧ (∀ (K : Type) [Field K] [CharZero K] (x y : Coefficient (rootsRepresentation K)), value K (x / y) = value K x / value K y) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a : ℚˣ) (β : K) (hroot : RepresentsRoot K z a β) (hz : classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) z = 0), ∃ b : ℚˣ, b ^ 19 = a) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a : ℚˣ) (β : K) (hroot : RepresentsRoot K z a β) (ha : ∃ b : ℚˣ, b ^ 19 = a), classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) z = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z : continuousCocycles (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) (a : ℚˣ) (β : K) (hroot : RepresentsRoot K z a β), classMap (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K)) z = 0 ↔ ∃ b : ℚˣ, b ^ 19 = a) := by
  exact ⟨MazurTransfer.OriginalContinuousRationalRootClassZeroCriterionProof20261019.value_ne_zero, MazurTransfer.OriginalContinuousRationalRootClassZeroCriterionProof20261019.value_injective, MazurTransfer.OriginalContinuousRationalRootClassZeroCriterionProof20261019.value_pow_nineteen, MazurTransfer.OriginalContinuousRationalRootClassZeroCriterionProof20261019.value_smul, MazurTransfer.OriginalContinuousRationalRootClassZeroCriterionProof20261019.value_div, MazurTransfer.OriginalContinuousRationalRootClassZeroCriterionProof20261019.rational_power_of_class_zero, MazurTransfer.OriginalContinuousRationalRootClassZeroCriterionProof20261019.class_zero_of_rational_power, MazurTransfer.OriginalContinuousRationalRootClassZeroCriterionProof20261019.class_zero_iff_rational_power⟩
#print axioms solution
