-- Prove2me | solution 1 for IsLocalRing.exists_units_forall_mul_const_pow_eq_mul_monomial_of_ringEquiv_adicCompletion_uvCrossingModel_of_forall_prime_mem_localization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6347bcc6-a555-5aaa-9c1f-e1e61b846372

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_mul_const_pow_eq_of_isUnit_of_isLocalization_away
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_units_forall_mul_const_pow_eq_mul_monomial_of_ringEquiv_adicCompletion_uvCrossingModel_of_forall_prime_mem_localization

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B]
    {K : Type*} [Field K] [Algebra B K] (hBK : Function.Injective (algebraMap B K))
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+* UVCrossingModel W (π ^ E))
    (ϖ : B) (k₀ : ℕ) (hk₀ : 1 ≤ k₀) (w₀ : (UVCrossingModel W (π ^ E))ˣ)
    (hϖ : ι (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) ϖ) =
      (w₀ : UVCrossingModel W (π ^ E)) * const (π ^ E) π ^ k₀)
    (f : K) (hf : f ≠ 0) (hfB : ∃ r₀ s₀ : B, s₀ ≠ 0 ∧ f * algebraMap B K s₀ = algebraMap B K r₀)
    (hunit : ∀ P : Ideal B, P.IsPrime → P ≠ ⊥ → ϖ ∉ P →
      (∃ r s : B, s ∉ P ∧ f * algebraMap B K s = algebraMap B K r) ∧
      (∃ r s : B, s ∉ P ∧ f⁻¹ * algebraMap B K s = algebraMap B K r)) :
    ∃ (w : (UVCrossingModel W (π ^ E))ˣ) (a b n k : ℕ), (a = 0 ∨ b = 0) ∧
      ∀ r s : B, f * algebraMap B K s = algebraMap B K r →
        ι (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) r) * const (π ^ E) π ^ k =
          ι (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) s) *
            ((w : UVCrossingModel W (π ^ E)) * U (π ^ E) ^ a * V (π ^ E) ^ b * const (π ^ E) π ^ n) := by
  classical

  obtain ⟨hdomM, -, hicM⟩ := ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow π hπ E hE
  haveI := hdomM
  haveI := hicM
  haveI : IsNoetherianRing (UVCrossingModel W (π ^ E)) := ModularCurve.UVCrossingModel.isNoetherianRing (π ^ E)
  set c : UVCrossingModel W (π ^ E) := const (π ^ E) π with hc_def
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hcE : c ^ E = const (π ^ E) (π ^ E) := by
    rw [hc_def, ← constHom_apply, ← constHom_apply, ← map_pow]
  have hc0 : c ≠ 0 := by
    have hmem : const (π ^ E) (π ^ E) ∈ nonZeroDivisors (UVCrossingModel W (π ^ E)) :=
      ModularCurve.UVCrossingModel.const_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hπ0))
    have hne : c ^ E ≠ 0 := by rw [hcE]; exact nonZeroDivisors.ne_zero hmem
    exact ne_zero_pow (by omega) hne
  have hcle : Submonoid.powers c ≤ nonZeroDivisors (UVCrossingModel W (π ^ E)) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hc0

  set S := Localization.Away c with hS_def
  haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hcle
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers c) S inferInstance
  haveI : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization S (Submonoid.powers c) hcle
  set Kh := FractionRing S with hKh_def

  set Bh := AdicCompletion (IsLocalRing.maximalIdeal B) B with hBh_def
  haveI : IsHausdorff (IsLocalRing.maximalIdeal B) B :=
    IsHausdorff.of_isLocalRing _ B (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  set j : B →+* UVCrossingModel W (π ^ E) := ι.toRingHom.comp (algebraMap B Bh) with hj_def
  have hj : ∀ b : B, j b = ι (algebraMap B Bh b) := fun b => rfl
  have hj_inj : Function.Injective j := by
    intro a b hab
    rw [hj, hj] at hab
    have h1 := ι.injective hab
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply] at h1
    exact AdicCompletion.of_injective _ _ h1
  set jS : B →+* S := (algebraMap (UVCrossingModel W (π ^ E)) S).comp j with hjS_def
  have hMS_inj : Function.Injective (algebraMap (UVCrossingModel W (π ^ E)) S) := IsLocalization.injective S hcle
  have hjS_inj : Function.Injective jS := hMS_inj.comp hj_inj
  set jK : B →+* Kh := (algebraMap S Kh).comp jS with hjK_def
  have hSK_inj : Function.Injective (algebraMap S Kh) := IsFractionRing.injective S Kh
  have hjK_inj : Function.Injective jK := hSK_inj.comp hjS_inj
  have hjK : ∀ b : B, jK b = algebraMap S Kh (jS b) := fun b => rfl

  obtain ⟨r₀, s₀, hs₀, hf₀⟩ := hfB
  have hr₀ : r₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hf₀
    rcases mul_eq_zero.mp hf₀ with h1 | h1
    · exact hf h1
    · exact hs₀ (hBK (by rw [h1, map_zero]))
  have hrel : ∀ r s : B, f * algebraMap B K s = algebraMap B K r → r * s₀ = r₀ * s := by
    intro r s hrs
    apply hBK
    rw [map_mul, map_mul, ← hrs, ← hf₀]
    ring
  have hjKs₀ : jK s₀ ≠ 0 := (map_ne_zero_iff jK hjK_inj).mpr hs₀
  have hjKr₀ : jK r₀ ≠ 0 := (map_ne_zero_iff jK hjK_inj).mpr hr₀
  set x : Kh := jK r₀ / jK s₀ with hx_def
  have hx0 : x ≠ 0 := div_ne_zero hjKr₀ hjKs₀
  have hxrel : ∀ r s : B, r * s₀ = r₀ * s → x * jK s = jK r := by
    intro r s h
    rw [hx_def, div_mul_eq_mul_div, div_eq_iff hjKs₀, ← map_mul, ← map_mul, ← h]
  have hxrel' : ∀ r s : B, s * s₀ = r₀ * r → x⁻¹ * jK s = jK r := by
    intro r s h
    rw [hx_def, inv_div, div_mul_eq_mul_div, div_eq_iff hjKr₀, ← map_mul, ← map_mul, mul_comm s₀ s, h, mul_comm r₀ r]

  have hϖS : IsUnit (jS ϖ) := by
    have h1 : jS ϖ = algebraMap (UVCrossingModel W (π ^ E)) S ((w₀ : UVCrossingModel W (π ^ E)) * c ^ k₀) := by
      show algebraMap _ S (j ϖ) = _
      rw [hj, hϖ]
    rw [h1, map_mul, map_pow]
    exact (w₀.isUnit.map _).mul ((IsLocalization.Away.algebraMap_isUnit c).pow _)

  have hH : ∀ (q : Ideal S) [q.IsPrime],
      (∃ r s : S, s ∉ q ∧ x * algebraMap S Kh s = algebraMap S Kh r) ∧
      (∃ r s : S, s ∉ q ∧ x⁻¹ * algebraMap S Kh s = algebraMap S Kh r) := by
    intro q hq
    set P : Ideal B := Ideal.comap jS q with hP_def
    have hPprime : P.IsPrime := Ideal.IsPrime.comap jS
    have hϖP : ϖ ∉ P := by
      rw [hP_def, Ideal.mem_comap]
      exact fun h => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ h hϖS)
    by_cases hP : P = ⊥
    · refine ⟨⟨jS r₀, jS s₀, ?_, ?_⟩, ⟨jS s₀, jS r₀, ?_, ?_⟩⟩
      · intro h; apply hs₀
        have : s₀ ∈ P := by rw [hP_def, Ideal.mem_comap]; exact h
        rwa [hP, Ideal.mem_bot] at this
      · rw [← hjK, ← hjK]; exact hxrel r₀ s₀ rfl
      · intro h; apply hr₀
        have : r₀ ∈ P := by rw [hP_def, Ideal.mem_comap]; exact h
        rwa [hP, Ideal.mem_bot] at this
      · rw [← hjK, ← hjK]; exact hxrel' s₀ r₀ rfl
    · obtain ⟨⟨r, s, hsP, hrs⟩, ⟨r', s', hs'P, hr's'⟩⟩ := hunit P hPprime hP hϖP
      refine ⟨⟨jS r, jS s, ?_, ?_⟩, ⟨jS r', jS s', ?_, ?_⟩⟩
      · intro h; exact hsP (by rw [hP_def, Ideal.mem_comap]; exact h)
      · rw [← hjK, ← hjK]; exact hxrel r s (hrel r s hrs)
      · intro h; exact hs'P (by rw [hP_def, Ideal.mem_comap]; exact h)
      · rw [← hjK, ← hjK]
        apply hxrel' r' s'

        have hfr' : f * algebraMap B K r' = algebraMap B K s' := by
          rw [← hr's', ← mul_assoc, mul_inv_cancel₀ hf, one_mul]
        exact hrel s' r' hfr'
  obtain ⟨φ, hφ⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one Kh x
    (fun q _ _ => (hH q).1)
  obtain ⟨ψ, hψ⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one Kh x⁻¹
    (fun q _ _ => (hH q).2)
  have hφunit : IsUnit φ := by
    refine IsUnit.of_mul_eq_one ψ (hSK_inj ?_)
    rw [map_mul, hφ, hψ, map_one, mul_inv_cancel₀ hx0]

  obtain ⟨w, a, b, n, k, hab, hmono⟩ :=
    ModularCurve.UVCrossingModel.exists_mul_const_pow_eq_of_isUnit_of_isLocalization_away π hπ E hE (S := S) φ hφunit
  refine ⟨w, a, b, n, k, hab, fun r s hrs => ?_⟩

  apply hMS_inj
  have hjr : jS r = jS s * φ := by
    apply hSK_inj
    rw [map_mul, hφ, ← hjK, ← hjK, mul_comm, hxrel r s (hrel r s hrs)]
  rw [map_mul, map_mul, map_pow, ← hj, ← hj]
  show jS r * (algebraMap _ S c) ^ k = jS s * algebraMap _ S ((w : UVCrossingModel W (π ^ E)) * U (π ^ E) ^ a * V (π ^ E) ^ b * c ^ n)
  rw [hjr, mul_assoc, hmono]

end S_IsLocalRing_exists_units_forall_mul_const_pow_eq_mul_monomial_of_ringEquiv_adicCompletion_uvCrossingModel_of_forall_prime_mem_localization
end P2MW
export P2MW.S_IsLocalRing_exists_units_forall_mul_const_pow_eq_mul_monomial_of_ringEquiv_adicCompletion_uvCrossingModel_of_forall_prime_mem_localization (solution)
