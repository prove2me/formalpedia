-- Prove2me | solution 1 for IsLocalRing.exists_mul_eq_pow_mul_and_isPrime_span_pair_and_height_eq_one_of_ringEquiv_adicCompletion_uvCrossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/0df1e522-68bf-5899-a459-73748be99862

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_V_powerSeries
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_le_two
import Theorems.Thm_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq
import Theorems.Thm_Ideal_comap_map_adicCompletion_eq_of_isNoetherianRing
import Theorems.Thm_Ideal_height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_mul_eq_pow_mul_and_isPrime_span_pair_and_height_eq_one_of_ringEquiv_adicCompletion_uvCrossingModel

set_option autoImplicit false

noncomputable section

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace TubeMaxVertical

section PowerSeriesMod

theorem exists_eq_C_mul_of_map_eq_zero {R : Type*} [CommRing R] {S : Type*} [CommRing S] (f : R →+* S) (a : R)
    (hker : ∀ r : R, f r = 0 → ∃ r' : R, r = a * r') (g : PowerSeries R) (hg : PowerSeries.map f g = 0) :
    ∃ h : PowerSeries R, g = PowerSeries.C a * h := by
  have hcoef : ∀ n : ℕ, ∃ b : R, PowerSeries.coeff n g = a * b := by
    intro n
    have := congrArg (PowerSeries.coeff n) hg
    rw [PowerSeries.coeff_map, map_zero] at this
    exact hker _ this
  choose b hb using hcoef
  refine ⟨PowerSeries.mk b, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hb]

end PowerSeriesMod

section Model

theorem const_pow' {W : Type*} [CommRing W] (s : W) (w : W) (n : ℕ) : const s (w ^ n) = const s w ^ n := by
  rw [← constHom_apply, map_pow]; rfl

theorem isPrime_span_const_V {W : Type*} [CommRing W] (π : W) (hπ : Prime π) (E : ℕ) (hE : 1 ≤ E) :
    (Ideal.span {const (π ^ E) π, V (π ^ E)}).IsPrime ∧
      U (π ^ E) ∉ Ideal.span {const (π ^ E) π, V (π ^ E)} ∧ ¬ IsUnit (U (π ^ E)) := by
  haveI : Nontrivial W := ⟨⟨π, 0, hπ.ne_zero⟩⟩
  obtain ⟨e, heU, heV, heC⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_V_powerSeries (W := W) (π ^ E)
  have hle : Ideal.span {π ^ E} ≤ Ideal.span {π} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact dvd_pow_self π (by omega)
  set fac : W ⧸ Ideal.span {π ^ E} →+* W ⧸ Ideal.span {π} := Ideal.Quotient.factor hle with hfac
  haveI : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  haveI : IsDomain (W ⧸ Ideal.span {π}) := (Ideal.Quotient.isDomain_iff_prime _).mpr inferInstance
  set Ψ : UVCrossingModel W (π ^ E) →+* PowerSeries (W ⧸ Ideal.span {π}) :=
    (PowerSeries.map fac).comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {V (π ^ E)}))) with hΨ
  have hΨ_apply : ∀ z, Ψ z = PowerSeries.map fac (e (Ideal.Quotient.mk (Ideal.span {V (π ^ E)}) z)) := fun _ => rfl
  have hΨU : Ψ (U (π ^ E)) = PowerSeries.X := by rw [hΨ_apply, heU, PowerSeries.map_X]
  have hΨV : Ψ (V (π ^ E)) = 0 := by rw [hΨ_apply, heV, map_zero]
  have hΨC : Ψ (const (π ^ E) π) = 0 := by
    rw [hΨ_apply, heC, PowerSeries.map_C, hfac, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π), map_zero]

  have hkerfac : ∀ r : W ⧸ Ideal.span {π ^ E}, fac r = 0 →
      ∃ r' : W ⧸ Ideal.span {π ^ E}, r = Ideal.Quotient.mk _ π * r' := by
    intro r hr
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [hfac, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hr
    obtain ⟨w', rfl⟩ := hr
    exact ⟨Ideal.Quotient.mk _ w', by rw [map_mul]⟩

  have hker : RingHom.ker Ψ = Ideal.span {const (π ^ E) π, V (π ^ E)} := by
    apply le_antisymm
    · intro z hz
      rw [RingHom.mem_ker, hΨ_apply] at hz
      obtain ⟨h, hh⟩ := exists_eq_C_mul_of_map_eq_zero fac (Ideal.Quotient.mk _ π) hkerfac _ hz
      obtain ⟨qbar, hq⟩ := e.surjective h
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective qbar
      have h1 : Ideal.Quotient.mk (Ideal.span {V (π ^ E)}) z =
          Ideal.Quotient.mk (Ideal.span {V (π ^ E)}) (const (π ^ E) π * q) := by
        apply e.injective
        rw [map_mul, map_mul, heC, hq]
        exact hh
      rw [Ideal.Quotient.eq] at h1
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h1
      have : z = q * const (π ^ E) π + r * V (π ^ E) := by
        rw [hr, mul_comm q]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    · rw [Ideal.span_le]
      rintro z (rfl | rfl)
      · exact hΨC
      · exact hΨV
  refine ⟨hker ▸ RingHom.ker_isPrime Ψ, ?_, ?_⟩
  · intro hU
    rw [← hker, RingHom.mem_ker, hΨU] at hU
    exact PowerSeries.X_ne_zero hU
  · intro hU
    have := hU.map Ψ
    rw [hΨU, PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X] at this
    exact not_isUnit_zero this

end Model

theorem three_le_ringKrullDim_of_chain {R : Type*} [CommRing R] (p₀ p₁ p₂ p₃ : PrimeSpectrum R)
    (h₀₁ : p₀ < p₁) (h₁₂ : p₁ < p₂) (h₂₃ : p₂ < p₃) : (3 : WithBot ℕ∞) ≤ ringKrullDim R := by
  let s : LTSeries (PrimeSpectrum R) :=
    (((RelSeries.singleton _ p₀).snoc p₁ (by simpa using h₀₁)).snoc p₂ (by simpa using h₁₂)).snoc p₃
      (by simpa using h₂₃)
  have hs : s.length = 3 := by simp [s]
  have := Order.LTSeries.length_le_krullDim s
  rw [hs] at this
  rw [ringKrullDim]
  exact_mod_cast this

end TubeMaxVertical

open TubeMaxVertical in
set_option maxHeartbeats 8000000 in
theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B]
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal B) B ≃+* UVCrossingModel W (π ^ E))
    (t x y : B)
    (ht : ι (algebraMap B (AdicCompletion (maximalIdeal B) B) t) = const (π ^ E) π)
    (γU γV : (UVCrossingModel W (π ^ E))ˣ)
    (hx : ι (algebraMap B (AdicCompletion (maximalIdeal B) B) x) = (γU : UVCrossingModel W (π ^ E)) * U (π ^ E))
    (hy : ι (algebraMap B (AdicCompletion (maximalIdeal B) B) y) = (γV : UVCrossingModel W (π ^ E)) * V (π ^ E)) :
    (∃ u : B, IsUnit u ∧ x * y = t ^ E * u) ∧
    (Ideal.span {t, y}).IsPrime ∧ x ∉ Ideal.span {t, y} ∧
    (∀ 𝔮 : Ideal B, 𝔮.IsPrime → t ∈ 𝔮 → x ∉ 𝔮 → 𝔮 ≠ maximalIdeal B → 𝔮 = Ideal.span {t, y}) ∧
    (Ideal.span {t, y}).height = 1 := by

  set j : B →+* UVCrossingModel W (π ^ E) :=
    ι.toRingHom.comp (algebraMap B (AdicCompletion (maximalIdeal B) B)) with hjdef
  have hj : ∀ b : B, j b = ι (algebraMap B (AdicCompletion (maximalIdeal B) B) b) := fun _ => rfl

  have hcontr : ∀ 𝔞 : Ideal B, (𝔞.map j).comap j = 𝔞 := by
    intro 𝔞
    rw [hjdef, ← Ideal.map_map, ← Ideal.comap_comap, Ideal.comap_map_of_bijective ι.toRingHom ι.bijective]
    exact Ideal.comap_map_adicCompletion_eq_of_isNoetherianRing 𝔞

  haveI hMdom : IsDomain (UVCrossingModel W (π ^ E)) :=
    (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ E hE).1
  set cπ : UVCrossingModel W (π ^ E) := const (π ^ E) π with hcπdef
  have hcπE : cπ ^ E = const (π ^ E) (π ^ E) := (const_pow' (π ^ E) π E).symm
  have hπE0 : π ^ E ∈ nonZeroDivisors W := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero E hπ.ne_zero)
  have hcπE0 : cπ ^ E ≠ 0 := by
    rw [hcπE]
    exact nonZeroDivisors.ne_zero (ModularCurve.UVCrossingModel.const_mem_nonZeroDivisors hπE0)
  have hcπ0 : cπ ≠ 0 := fun h => hcπE0 (by rw [h, zero_pow (by omega)])
  have hjt : j t = cπ := by rw [hj, ht]
  have ht0 : t ≠ 0 := fun h => hcπ0 (by rw [← hjt, h, map_zero])

  have hπprime : Prime π := hπ.prime
  obtain ⟨hPVprime, hUnot, hUnu⟩ := isPrime_span_const_V π hπprime E hE

  have hUV : U (π ^ E) * V (π ^ E) = cπ ^ E := by
    rw [ModularCurve.UVCrossingModel.U_mul_V, hcπE]
  have hjxy : j (x * y) = j (t ^ E) * ((γU * γV : (UVCrossingModel W (π ^ E))ˣ) : UVCrossingModel W (π ^ E)) := by
    rw [map_mul, hj x, hj y, hx, hy, map_pow, hjt, Units.val_mul, mul_mul_mul_comm, hUV, mul_comm]
  have hmem : x * y ∈ ((Ideal.span {t ^ E}).map j).comap j := by
    rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton, hjxy]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  rw [hcontr] at hmem
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hmem
  have hju : j u = ((γU * γV : (UVCrossingModel W (π ^ E))ˣ) : UVCrossingModel W (π ^ E)) := by
    have h1 : j (t ^ E) * j u = j (t ^ E) * ((γU * γV : (UVCrossingModel W (π ^ E))ˣ) : UVCrossingModel W (π ^ E)) := by
      rw [← map_mul, mul_comm, hu, hjxy]
    have h2 : j (t ^ E) ≠ 0 := by rw [map_pow, hjt]; exact hcπE0
    exact mul_left_cancel₀ h2 h1
  have huunit : IsUnit u := by
    have h1 : (Ideal.span {u}).map j = ⊤ := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top, hju]
      exact Units.isUnit _
    have h2 := hcontr (Ideal.span {u})
    rw [h1, Ideal.comap_top] at h2
    exact Ideal.span_singleton_eq_top.mp h2.symm
  have hnode : x * y = t ^ E * u := by rw [← hu, mul_comm]

  have hmapP : (Ideal.span {t, y}).map j = Ideal.span {cπ, V (π ^ E)} := by
    rw [Ideal.map_span, Set.image_pair, hjt, hj y, hy]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro z (rfl | rfl)
      · exact Ideal.subset_span (Set.mem_insert _ _)
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    · rw [Ideal.span_le]
      rintro z (rfl | rfl)
      · exact Ideal.subset_span (Set.mem_insert _ _)
      · have hmem : ((γV⁻¹ : (UVCrossingModel W (π ^ E))ˣ) : UVCrossingModel W (π ^ E)) *
            ((γV : UVCrossingModel W (π ^ E)) * V (π ^ E)) ∈
            Ideal.span {cπ, (γV : UVCrossingModel W (π ^ E)) * V (π ^ E)} :=
          Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        rwa [← mul_assoc, Units.inv_mul, one_mul] at hmem
  have hPprime : (Ideal.span {t, y}).IsPrime := by
    rw [← hcontr (Ideal.span {t, y}), hmapP]
    haveI := hPVprime
    exact Ideal.comap_isPrime j _
  have hxP : x ∉ Ideal.span {t, y} := by
    intro hxm
    have h1 : j x ∈ (Ideal.span {t, y}).map j := Ideal.mem_map_of_mem j hxm
    rw [hmapP, hj x, hx] at h1
    apply hUnot
    have : U (π ^ E) = ((γU⁻¹ : (UVCrossingModel W (π ^ E))ˣ) : UVCrossingModel W (π ^ E)) *
        ((γU : UVCrossingModel W (π ^ E)) * U (π ^ E)) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ h1

  have hdim : ringKrullDim B ≤ 2 := by
    rw [← IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq B, ringKrullDim_eq_of_ringEquiv ι]
    exact ModularCurve.UVCrossingModel.ringKrullDim_le_two π hπ E hE
  have hP0 : Ideal.span {t, y} ≠ ⊥ := by
    intro h
    apply ht0
    have : t ∈ Ideal.span {t, y} := Ideal.subset_span (Set.mem_insert _ _)
    rw [h, Ideal.mem_bot] at this
    exact this
  have hxm : x ∈ maximalIdeal B := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hxu
    have h1 : IsUnit (j x) := hxu.map j
    rw [hj x, hx] at h1
    exact hUnu (isUnit_of_mul_isUnit_right h1)
  have hPm : Ideal.span {t, y} ≠ maximalIdeal B := fun h => hxP (h ▸ hxm)
  haveI := hPprime

  have hht : (Ideal.span {t, y}).height = 1 :=
    Ideal.height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two hdim _ hP0
      (fun hmax => hPm (IsLocalRing.eq_maximalIdeal hmax))
  refine ⟨⟨u, huunit, hnode⟩, hPprime, hxP, ?_, hht⟩

  intro 𝔮 h𝔮 ht𝔮 hx𝔮 h𝔮m
  have hy𝔮 : y ∈ 𝔮 := by
    have : x * y ∈ 𝔮 := by
      rw [hnode]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem 𝔮 ht𝔮 E (by omega))
    exact (h𝔮.mem_or_mem this).resolve_left hx𝔮
  have hle : Ideal.span {t, y} ≤ 𝔮 := by
    rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact ht𝔮
    · exact hy𝔮
  by_contra hne
  have hlt : Ideal.span {t, y} < 𝔮 := lt_of_le_of_ne hle (Ne.symm hne)
  have h𝔮lt : 𝔮 < maximalIdeal B := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal h𝔮.ne_top) h𝔮m
  have hbot : (⊥ : Ideal B) < Ideal.span {t, y} := lt_of_le_of_ne bot_le (Ne.symm hP0)
  have h3 := three_le_ringKrullDim_of_chain (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ⟨Ideal.span {t, y}, hPprime⟩
    ⟨𝔮, h𝔮⟩ ⟨maximalIdeal B, inferInstance⟩ hbot hlt h𝔮lt
  have : (3 : WithBot ℕ∞) ≤ 2 := h3.trans hdim
  exact absurd this (by norm_num)

end

end S_IsLocalRing_exists_mul_eq_pow_mul_and_isPrime_span_pair_and_height_eq_one_of_ringEquiv_adicCompletion_uvCrossingModel
end P2MW
export P2MW.S_IsLocalRing_exists_mul_eq_pow_mul_and_isPrime_span_pair_and_height_eq_one_of_ringEquiv_adicCompletion_uvCrossingModel (solution)
