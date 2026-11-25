-- Prove2me | solution 1 for GlobalTheory.LatOrb.exists_unitary_matLat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:43:22.444799+00:00
-- url     : https://prove2.me/submissions/b47aa7e9-6798-4169-a67e-256b9dc04fa5

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralMatrixOfMapsToFullRankLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryAdjoinLatticeImageEq
import Theorems.Thm_GlobalTheory_LatOrb_exists_mul_eq_one_mem
import Theorems.Thm_GlobalTheory_LatOrb_conjTranspose_mem_adjoin
import Theorems.Thm_GlobalTheory_LatOrb_aeval_map_mulVec_mem
import Theorems.Thm_GlobalTheory_LatOrb_matLat_le
import Theorems.Thm_GlobalTheory_LatOrb_matLat_mono
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
import Theorems.Thm_GlobalTheory_LatOrb_matLat_mul
import Theorems.Thm_GlobalTheory_LatOrb_mem_matLat
import Theorems.Thm_GlobalTheory_T_exists_unitary_mul_integral_of_norm_maximalOrder_unit
import Theorems.Thm_GlobalTheory_T_integral_aeval_eq_aeval_map_of_coprime_charpoly
import Theorems.Thm_GlobalTheory_T_isIntegral_matrix_of_mapsTo_fullRankLattice
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
noncomputable section
open GlobalTheory GlobalTheory.LatOrb
namespace GlobalTheory.LatOrb
theorem _root_.solution : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ σ : K →+* K, (∀ x, σ (σ x) = x) → (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    (γ.map σ)ᵀ * γ = 1 →
    ∀ M : Submodule O (Fin n → K), IsLatV O M → (∀ v ∈ M, γ *ᵥ v ∈ M) →
    ∀ p : K[X], IsUnit (aeval γ p) → matLat O (((aeval γ p).map σ)ᵀ * aeval γ p) M = M →
    ∃ t : Matrix (Fin n) (Fin n) K, (t.map σ)ᵀ * t = 1 ∧ t * γ = γ * t ∧
      matLat O t M = matLat O (aeval γ p) M := by
  intro O K _ _ _ _ _ _ _ n P₀ hcop γ hchar σ hσ hσO hγ M hML hMγ p hpu hpM
  set A := Algebra.adjoin K {γ} with hAdef
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := by
    have hc : ∀ a ∈ ({γ} : Set (Matrix (Fin n) (Fin n) K)), ∀ b ∈ ({γ} : Set _), a * b = b * a := by
      intro a ha b hb; rw [Set.mem_singleton_iff] at ha hb; rw [ha, hb]
    letI : CommRing A := Algebra.adjoinCommRingOfComm K hc
    intro u hu v hv
    exact congrArg Subtype.val (mul_comm (⟨u, hu⟩ : A) ⟨v, hv⟩)
  letI : CommRing A := Algebra.adjoinCommRingOfComm K (by
    intro a ha b hb; rw [Set.mem_singleton_iff] at ha hb; rw [ha, hb])
  have hstar : ∀ a ∈ A, (a.map σ)ᵀ ∈ A := fun a ha => conjTranspose_mem_adjoin σ γ hγ ha
  let τ : A →+* A :=
    { toFun := fun a => ⟨(a.1.map σ)ᵀ, hstar a.1 a.2⟩
      map_one' := by
        apply Subtype.ext
        show (((1 : Matrix (Fin n) (Fin n) K)).map σ)ᵀ = 1
        rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
      map_mul' := fun a b => by
        apply Subtype.ext
        show ((a.1 * b.1).map σ)ᵀ = (a.1.map σ)ᵀ * (b.1.map σ)ᵀ
        rw [Matrix.map_mul, Matrix.transpose_mul]
        exact hcomm _ (hstar b.1 b.2) _ (hstar a.1 a.2)
      map_zero' := by
        apply Subtype.ext
        show (((0 : Matrix (Fin n) (Fin n) K)).map σ)ᵀ = 0
        rw [Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero]
      map_add' := fun a b => by
        apply Subtype.ext
        show ((a.1 + b.1).map σ)ᵀ = (a.1.map σ)ᵀ + (b.1.map σ)ᵀ
        rw [Matrix.map_add _ (map_add σ), Matrix.transpose_add] }
  have hτv : ∀ a : A, (τ a).1 = (a.1.map σ)ᵀ := fun a => rfl
  have hττ : ∀ a, τ (τ a) = a := by
    intro a; apply Subtype.ext
    rw [hτv, hτv, Matrix.transpose_map, Matrix.map_map, Matrix.transpose_transpose]
    ext i j; simp [hσ]
  have hτk : ∀ k, τ (algebraMap K A k) = algebraMap K A (σ k) := by
    intro k; apply Subtype.ext
    rw [hτv]
    show ((algebraMap K (Matrix (Fin n) (Fin n) K) k).map σ)ᵀ = algebraMap K (Matrix (Fin n) (Fin n) K) (σ k)
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]

  have hred : IsReduced A := by
    constructor
    rintro a ⟨k, hk⟩
    obtain ⟨q, hq⟩ : ∃ q, aeval γ q = a.1 := by
      exact (Algebra.adjoin_singleton_eq_range_aeval K γ).le a.2
    have h1 : aeval γ (q ^ k) = 0 := by
      rw [map_pow, hq]; exact congrArg Subtype.val hk
    have hsep : (minpoly K γ).Separable :=
      ((show P₀.Separable from hcop).map (f := algebraMap O K)).of_dvd
        (hchar ▸ Matrix.minpoly_dvd_charpoly γ)
    have h2 : minpoly K γ ∣ q := hsep.squarefree.isRadical k q (minpoly.dvd K γ h1)
    apply Subtype.ext
    rw [← hq]
    exact Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero h2 (minpoly.aeval K γ)

  have hxA : aeval γ p ∈ A := Polynomial.aeval_mem_adjoin_singleton K γ
  obtain ⟨b, hbA, hb⟩ := exists_mul_eq_one_mem A hxA (fun b hb => by
    obtain ⟨u, hu⟩ := hpu
    rw [← hu] at hb
    rw [← Matrix.one_mul b, ← u.inv_mul, Matrix.mul_assoc, hb, Matrix.mul_zero])
  let x : Aˣ := Units.mkOfMulEqOne (⟨aeval γ p, hxA⟩ : A) ⟨b, hbA⟩ (Subtype.ext hb)
  have hxv : ((x : A) : Matrix (Fin n) (Fin n) K) = aeval γ p := rfl
  let ι : A →ₐ[O] Matrix (Fin n) (Fin n) K := (A.val).restrictScalars O
  have hι : ∀ a : A, IsIntegral O a ↔ IsIntegral O a.1 := fun a =>
    (isIntegral_algHom_iff ι Subtype.val_injective).symm

  have hcM : ∀ v ∈ M, (τ x * x : A).1 *ᵥ v ∈ M := by
    intro v hv
    have : (τ x * x : A).1 *ᵥ v ∈ matLat O (((aeval γ p).map σ)ᵀ * aeval γ p) M :=
      (mem_matLat _ _ _).mpr ⟨v, hv, rfl⟩
    rwa [hpM] at this
  have hcinv : (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A)) * (τ x * x) = 1 := by
    rw [mul_mul_mul_comm, ← map_mul, Units.inv_mul, map_one, one_mul]
  have hc'M : ∀ v ∈ M, (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A) : A).1 *ᵥ v ∈ M := by
    intro v hv
    rw [← hpM] at hv
    obtain ⟨u, hu, rfl⟩ := (mem_matLat _ _ _).mp hv
    have e : ((τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A) : A).1 *ᵥ ((((aeval γ p).map σ)ᵀ * aeval γ p) *ᵥ u)) = u := by
      rw [Matrix.mulVec_mulVec]
      have := congrArg Subtype.val hcinv
      exact (congrArg (· *ᵥ u) this).trans (Matrix.one_mulVec u)
    rw [e]; exact hu
  have hi1 : IsIntegral O (τ (x : A) * x) := (hι _).mpr (GlobalTheory.T.isIntegral_matrix_of_mapsTo_fullRankLattice n M hML _ hcM)
  have hi2 : IsIntegral O (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A)) :=
    (hι _).mpr (GlobalTheory.T.isIntegral_matrix_of_mapsTo_fullRankLattice n M hML _ hc'M)
  obtain ⟨t, ht1, ht2, ht3⟩ := GlobalTheory.T.exists_unitary_mul_integral_of_norm_maximalOrder_unit σ hσO τ hττ hτk x hi1 hi2

  have hkeep : ∀ a : A, IsIntegral O a → ∀ v ∈ M, a.1 *ᵥ v ∈ M := by
    intro a ha
    obtain ⟨q, hq⟩ : ∃ q, aeval γ q = a.1 := by
      exact (Algebra.adjoin_singleton_eq_range_aeval K γ).le a.2
    have ha' : IsIntegral O (aeval γ q) := hq ▸ (hι a).mp ha
    obtain ⟨r, hr⟩ := GlobalTheory.T.integral_aeval_eq_aeval_map_of_coprime_charpoly n P₀ hcop γ hchar q ha'
    rw [← hq, hr]
    exact aeval_map_mulVec_mem M γ hMγ r
  have hk1 := hkeep _ ht2
  have hk2 := hkeep _ ht3
  refine ⟨(t : A).1, congrArg Subtype.val ht1, hcomm _ (t : A).2 _ (Algebra.subset_adjoin rfl), ?_⟩
  apply le_antisymm
  · have e : (t : A).1 = (aeval γ p) * ((t : A) * ((x⁻¹ : Aˣ) : A)).1 := by
      rw [← hxv]
      show (t : A).1 = ((x : A) * ((t : A) * ((x⁻¹ : Aˣ) : A))).1
      rw [mul_comm (t : A), ← mul_assoc, Units.mul_inv, one_mul]
    rw [e, matLat_mul]
    exact matLat_mono _ (matLat_le M _ hk1)
  · have e : aeval γ p = (t : A).1 * (((t⁻¹ : Aˣ) : A) * (x : A)).1 := by
      rw [← hxv]
      show ((x : A)).1 = ((t : A) * (((t⁻¹ : Aˣ) : A) * (x : A))).1
      rw [← mul_assoc, Units.mul_inv, one_mul]
    rw [e, matLat_mul]
    exact matLat_mono _ (matLat_le M _ hk2)
end GlobalTheory.LatOrb
