-- Prove2me | solution 1 for GlobalTheory.GaloisPowerRoots.exists_pow_eq_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:29:27.402439+00:00
-- url     : https://prove2.me/submissions/dc50d046-57e3-497a-b1d1-ea0dc175dc2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
import Theorems.Thm_GlobalTheory_GaloisPowerRoots_isLocalRing_of_isInvariant
import Theorems.Thm_GlobalTheory_GaloisPowerRoots_exists_sub_mem_maximalIdeal
import Theorems.Thm_GlobalTheory_GaloisPowerRoots_exists_unit_mul_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Polynomial IsLocalRing
open scoped Pointwise
open GlobalTheory GlobalTheory.GaloisPowerRoots
namespace GlobalTheory.GaloisPowerRoots
theorem _root_.solution {R : Type*} (K L M : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [Algebra R K]
    [IsFractionRing R K] {π : R} (hπ : Irreducible π) [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (hn : IsUnit (Module.finrank K L : R))
    [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois K M]
    [FiniteDimensional K M] (ρ : M)
    (hρ : ρ ^ Module.finrank K L = algebraMap K M (algebraMap R K π)) :
    ∃ ρ : L, ρ ^ Module.finrank K L = algebraMap K L (algebraMap R K π) := by
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra R M := ((algebraMap K M).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R L M := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply K L M (algebraMap R K x)
  set n := Module.finrank K L with hn'
  have hn0 : 0 < n := Module.finrank_pos
  set T := integralClosure R M
  set S := integralClosure R L
  haveI : FaithfulSMul R M := FaithfulSMul.trans R K M
  haveI : FaithfulSMul R T := FaithfulSMul.tower_bot R T M
  haveI : Algebra.IsInvariant R T (M ≃ₐ[K] M) := ⟨fun x hx => by
    have h1 : (x : M) ∈ (⊥ : IntermediateField K M) :=
      (IsGalois.mem_bot_iff_fixed _).mpr fun σ => congrArg Subtype.val (hx σ)
    obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp h1
    have h2 : IsIntegral R z := by
      rw [← isIntegral_algebraMap_iff (algebraMap K M).injective, hz]; exact x.2
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
    refine ⟨r, Subtype.ext ?_⟩
    rw [← hz, ← hr]; rfl⟩
  haveI : IsLocalRing T := isLocalRing_of_isInvariant (A := R) (G := M ≃ₐ[K] M)
  let ι : S →+* T := ((algebraMap L M).comp (algebraMap S L)).codRestrict
    T.toSubring (fun x => (x.2 : IsIntegral R (x : L)).algebraMap)
  have hι : ∀ x : S, ((ι x : T) : M) = algebraMap L M x := fun _ => rfl
  have hunit : ∀ x : S, IsUnit (ι x) → IsUnit x := by
    intro x hx
    obtain ⟨z, hz⟩ := hx.exists_right_inv
    have hz' : algebraMap L M x * (z : M) = 1 := congrArg Subtype.val hz
    have hx0 : (x : L) ≠ 0 := fun h => by simp [h] at hz'
    have h3 : algebraMap L M (x : L)⁻¹ = z := by
      rw [map_inv₀]; exact inv_eq_of_mul_eq_one_right hz'
    have h4 : IsIntegral R (x : L)⁻¹ := by
      rw [← isIntegral_algebraMap_iff (algebraMap L M).injective, h3]; exact z.2
    exact IsUnit.of_mul_eq_one (⟨_, h4⟩ : S) (Subtype.ext (mul_inv_cancel₀ hx0))
  haveI : IsLocalRing S := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (ι x) with h | h
    · exact Or.inl (hunit _ h)
    · exact Or.inr (hunit _ (by simpa using h))
  obtain ⟨u, ϖ, hu⟩ := exists_unit_mul_pow K L hπ
  have hu' : algebraMap K L (algebraMap R K π) = ((u : S) : L) * (ϖ : L) ^ n :=
    congrArg Subtype.val hu
  have hπ0 : algebraMap K L (algebraMap R K π) ≠ 0 := by simpa using hπ.ne_zero
  have hϖ0 : (ϖ : L) ≠ 0 := fun h => hπ0 (by rw [hu', h, zero_pow hn0.ne', mul_zero])
  have hϖ1 : algebraMap L M ϖ ≠ 0 := by simpa using hϖ0
  have hy : (ρ / algebraMap L M ϖ) ^ n = (ι u : T) := by
    rw [div_pow, hρ, IsScalarTower.algebraMap_apply K L M, hu', hι, map_mul, map_pow]
    field_simp
  have hyint : IsIntegral R (ρ / algebraMap L M ϖ) :=
    IsIntegral.of_pow hn0 (by rw [hy]; exact (ι u).2)
  set y : T := ⟨_, hyint⟩ with hydef
  have hyn : y ^ n = ι u := Subtype.ext hy
  have hyu : IsUnit y := (isUnit_pow_iff hn0.ne').mp (by rw [hyn]; exact u.isUnit.map ι)
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  haveI : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
  have hfix : ∀ σ : M ≃ₐ[L] M, σ (y : M) = y := by
    intro σ
    let τ : M ≃ₐ[K] M := σ.restrictScalars K
    obtain ⟨a, ha⟩ := exists_sub_mem_maximalIdeal (A := R) y
    have ha2 : τ • y - algebraMap R T a ∈ maximalIdeal T := by
      rw [← smul_algebraMap τ a, ← smul_sub]
      intro h
      apply ha
      have := h.map (MulSemiringAction.toRingHom _ T τ⁻¹)
      rwa [MulSemiringAction.toRingHom_apply, inv_smul_smul] at this
    have hres : residue T (τ • y) = residue T y := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      simpa using (maximalIdeal T).sub_mem ha2 ha
    have hpow : (τ • y) ^ n = y ^ n := by
      rw [← smul_pow', hyn]
      exact Subtype.ext (σ.commutes _)
    have h5 := geom_sum₂_mul (τ • y) y n
    rw [hpow, sub_self, mul_eq_zero] at h5
    rcases h5 with h5 | h5
    · exfalso
      have h6 := congrArg (residue T) h5
      simp only [map_sum, map_mul, map_pow, hres, map_zero] at h6
      rw [geom_sum₂_self] at h6
      have h7 : IsUnit ((n : ResidueField T) * residue T y ^ (n - 1)) := by
        refine IsUnit.mul ?_ ((hyu.map _).pow _)
        simpa using (hn.map (algebraMap R T)).map (residue T)
      exact h7.ne_zero h6
    · exact congrArg Subtype.val (sub_eq_zero.mp h5)
  obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed _).mpr hfix)
  refine ⟨z * ϖ, (algebraMap L M).injective ?_⟩
  rw [map_pow, map_mul, hz, ← IsScalarTower.algebraMap_apply K L M, ← hρ]
  congr 1
  exact div_mul_cancel₀ _ hϖ1
end GlobalTheory.GaloisPowerRoots
