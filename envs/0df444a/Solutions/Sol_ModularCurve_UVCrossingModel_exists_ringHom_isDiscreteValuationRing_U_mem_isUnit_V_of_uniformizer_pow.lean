-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_ringHom_isDiscreteValuationRing_U_mem_isUnit_V_of_uniformizer_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9bc65631-89e2-57af-b6f4-bdcc74f355fa

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_ringHom_isDiscreteValuationRing_U_mem_isUnit_V_of_uniformizer_pow

set_option autoImplicit false
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem solution
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsDiscreteValuationRing D)
      (ψ : UVCrossingModel W (ϖ ^ e) →+* D),
      Function.Injective ψ ∧
      ψ (U (ϖ ^ e)) ∈ maximalIdeal D ∧
      IsUnit (ψ (V (ϖ ^ e))) ∧
      maximalIdeal D = Ideal.span {ψ (const (ϖ ^ e) ϖ)} ∧
      (∀ x : UVCrossingModel W (ϖ ^ e), ψ x ∈ maximalIdeal D ↔ x ∈ Ideal.span {U (ϖ ^ e), const (ϖ ^ e) ϖ})  := by
  classical
  have he0 : e ≠ 0 := by omega

  obtain ⟨iMd, iMl, -⟩ := ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete ϖ hϖ e he
  haveI := iMd; haveI := iMl
  haveI : IsNoetherianRing (UVCrossingModel W (ϖ ^ e)) := ModularCurve.UVCrossingModel.isNoetherianRing _

  have hprime : (Ideal.span {ϖ} : Ideal W).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).mpr hϖ.prime
  haveI : IsDomain (W ⧸ Ideal.span {ϖ}) := (Ideal.Quotient.isDomain_iff_prime _).mpr hprime

  let red : (W ⧸ Ideal.span {ϖ ^ e}) →+* (W ⧸ Ideal.span {ϖ}) :=
    Ideal.Quotient.lift (Ideal.span {ϖ ^ e}) (Ideal.Quotient.mk (Ideal.span {ϖ})) (fun a ha => by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self ϖ he0) ha)
  have hred : ∀ a : W, red (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := fun a => rfl
  have hredker : ∀ t : W ⧸ Ideal.span {ϖ ^ e}, red t = 0 → ∃ c : W ⧸ Ideal.span {ϖ ^ e}, t = Ideal.Quotient.mk _ ϖ * c := by
    intro t ht
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
    rw [hred, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at ht
    obtain ⟨c, rfl⟩ := ht
    exact ⟨Ideal.Quotient.mk _ c, by rw [map_mul]⟩

  obtain ⟨eU, heV, heU, heC⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_U_powerSeries (ϖ ^ e)
  let ρ : UVCrossingModel W (ϖ ^ e) →+* PowerSeries (W ⧸ Ideal.span {ϖ}) :=
    (PowerSeries.map red).comp (eU.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {U (ϖ ^ e)})))
  have hρ : ∀ x, ρ x = PowerSeries.map red (eU (Ideal.Quotient.mk (Ideal.span {U (ϖ ^ e)}) x)) := fun _ => rfl
  let 𝔔 : Ideal (UVCrossingModel W (ϖ ^ e)) := RingHom.ker ρ
  haveI h𝔔 : 𝔔.IsPrime := RingHom.ker_isPrime ρ
  have hρU : ρ (U (ϖ ^ e)) = 0 := by rw [hρ, heU, map_zero]
  have hρc : ρ (const (ϖ ^ e) ϖ) = 0 := by
    rw [hρ, heC, PowerSeries.map_C, hred, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), map_zero]
  have hρV : ρ (V (ϖ ^ e)) = PowerSeries.X := by rw [hρ, heV, PowerSeries.map_X]
  have hVQ : V (ϖ ^ e) ∉ 𝔔 := by
    show ρ (V (ϖ ^ e)) ≠ 0
    rw [hρV]; exact PowerSeries.X_ne_zero

  have hQ : ∀ x : UVCrossingModel W (ϖ ^ e), x ∈ 𝔔 ↔ x ∈ Ideal.span {U (ϖ ^ e), const (ϖ ^ e) ϖ} := by
    intro x
    constructor
    · intro hx
      have hx' : PowerSeries.map red (eU (Ideal.Quotient.mk (Ideal.span {U (ϖ ^ e)}) x)) = 0 := hx
      set f := eU (Ideal.Quotient.mk (Ideal.span {U (ϖ ^ e)}) x) with hf
      have hcoef : ∀ n, ∃ c : W ⧸ Ideal.span {ϖ ^ e}, PowerSeries.coeff n f = Ideal.Quotient.mk _ ϖ * c := by
        intro n
        apply hredker
        have := congrArg (PowerSeries.coeff n) hx'
        rwa [PowerSeries.coeff_map, map_zero] at this
      choose c hc using hcoef
      let g : PowerSeries (W ⧸ Ideal.span {ϖ ^ e}) := PowerSeries.mk c
      have hfg : f = PowerSeries.C (Ideal.Quotient.mk _ ϖ) * g := by
        ext n; rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]; exact hc n
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {U (ϖ ^ e)}) (eU.symm g)
      have hxy : Ideal.Quotient.mk (Ideal.span {U (ϖ ^ e)}) (x - const (ϖ ^ e) ϖ * y) = 0 := by
        rw [map_sub, map_mul]
        apply eU.injective
        rw [map_sub, map_mul, heC, hy, RingEquiv.apply_symm_apply, map_zero, ← hf, hfg, sub_self]
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hxy
      obtain ⟨z, hz⟩ := hxy
      rw [Ideal.mem_span_pair]
      exact ⟨z, y, by rw [mul_comm z, ← hz, mul_comm y]; ring⟩
    · intro hx
      refine (Ideal.span_le (I := 𝔔)).mpr ?_ hx
      rintro z (rfl | rfl)
      · exact hρU
      · exact hρc

  let D := Localization.AtPrime 𝔔
  have hS : 𝔔.primeCompl ≤ nonZeroDivisors (UVCrossingModel W (ϖ ^ e)) :=
    le_nonZeroDivisors_of_noZeroDivisors (fun (h0 : (0 : UVCrossingModel W (ϖ ^ e)) ∈ 𝔔.primeCompl) => h0 (Ideal.zero_mem 𝔔))
  have hinj : Function.Injective (algebraMap (UVCrossingModel W (ϖ ^ e)) D) :=
    IsLocalization.injective (M := 𝔔.primeCompl) D hS
  have hmem : ∀ x, algebraMap _ D x ∈ maximalIdeal D ↔ x ∈ 𝔔 := fun x => IsLocalization.AtPrime.to_map_mem_maximal_iff D 𝔔 x
  have hψV : IsUnit (algebraMap _ D (V (ϖ ^ e))) := by
    by_contra hu; exact hVQ ((hmem _).mp ((IsLocalRing.mem_maximalIdeal _).mpr hu))
  have hψU : algebraMap _ D (U (ϖ ^ e)) ∈ maximalIdeal D := (hmem _).mpr (RingHom.mem_ker.mpr hρU)
  have hcpow : const (ϖ ^ e) (ϖ ^ e) = (const (ϖ ^ e) ϖ) ^ e := by
    rw [← constHom_apply, ← constHom_apply, map_pow]
  have hUmem : algebraMap _ D (U (ϖ ^ e)) ∈ Ideal.span {algebraMap _ D (const (ϖ ^ e) ϖ)} := by
    obtain ⟨w, hw⟩ := hψV
    have hUV : algebraMap _ D (U (ϖ ^ e)) * algebraMap _ D (V (ϖ ^ e)) = (algebraMap _ D (const (ϖ ^ e) ϖ)) ^ e := by
      rw [← map_mul, ModularCurve.UVCrossingModel.U_mul_V, hcpow, map_pow]
    have : algebraMap _ D (U (ϖ ^ e)) = (algebraMap _ D (const (ϖ ^ e) ϖ)) ^ e * ((w⁻¹ : Dˣ) : D) := by
      rw [← hUV, ← hw, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_left (dvd_pow_self _ he0) _)
  have hmax : maximalIdeal D = Ideal.span {algebraMap _ D (const (ϖ ^ e) ϖ)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [hQ, Ideal.mem_span_pair] at hx
      obtain ⟨a, b', rfl⟩ := hx
      show algebraMap _ D (a * U (ϖ ^ e) + b' * const (ϖ ^ e) ϖ) ∈ Ideal.span {algebraMap _ D (const (ϖ ^ e) ϖ)}
      rw [map_add, map_mul, map_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hUmem) (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr hρc)
  have hc0 : algebraMap _ D (const (ϖ ^ e) ϖ) ≠ 0 := by
    intro h0
    have h1 : const (ϖ ^ e) ϖ = 0 := hinj (by rw [h0, map_zero])
    have h2 : const (ϖ ^ e) (ϖ ^ e) = 0 := by rw [hcpow, h1, zero_pow he0]
    have hnd := ModularCurve.UVCrossingModel.const_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero e hϖ.ne_zero) : ϖ ^ e ∈ nonZeroDivisors W)
    exact (nonZeroDivisors.ne_zero hnd) h2
  have hnf : ¬ IsField D := by
    intro hF
    have := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hF
    rw [hmax, Ideal.span_singleton_eq_bot] at this
    exact hc0 this
  have hpr : (maximalIdeal D).IsPrincipal :=
    ⟨⟨algebraMap _ D (const (ϖ ^ e) ϖ), by rw [hmax, Ideal.submodule_span_eq]⟩⟩
  have hdvr : IsDiscreteValuationRing D := ((IsDiscreteValuationRing.TFAE D hnf).out 0 4).mpr hpr
  refine ⟨D, inferInstance, inferInstance, hdvr, algebraMap _ D, hinj, hψU, hψV, hmax, fun x => ?_⟩
  rw [hmem, hQ]

end S_ModularCurve_UVCrossingModel_exists_ringHom_isDiscreteValuationRing_U_mem_isUnit_V_of_uniformizer_pow
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_ringHom_isDiscreteValuationRing_U_mem_isUnit_V_of_uniformizer_pow (solution)
