-- Prove2me | solution 1 for IsLocalRing.isReduced_quotient_map_of_flat_of_locallyPrincipalOverring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c0b7e517-6030-514c-ae42-2c0290478c89

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isReduced_quotient_map_of_flat_of_locallyPrincipalOverring

set_option autoImplicit false

open IsLocalRing TensorProduct

namespace R1AF8H1

theorem isReduced_of_maximalIdeal_eq_span {L : Type*} [CommRing L] [IsLocalRing L] [IsNoetherianRing L]
    (τ : L) (hτ : maximalIdeal L = Ideal.span {τ}) (hreg : τ = 0 ∨ τ ∈ nonZeroDivisors L) :
    IsReduced L := by
  classical
  rcases hreg with hzero | hreg
  ·
    have hbot : maximalIdeal L = ⊥ := by rw [hτ, hzero, Ideal.span_singleton_eq_bot]
    have hf : IsField L := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot
    letI := hf.toField
    infer_instance
  refine ⟨fun x hx => ?_⟩
  by_contra hx0

  have hKrull : (⨅ n : ℕ, maximalIdeal L ^ n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal L).ne_top
  have hex : ∃ n : ℕ, x ∉ maximalIdeal L ^ n := by
    by_contra h
    push Not at h
    have : x ∈ (⨅ n : ℕ, maximalIdeal L ^ n) := Ideal.mem_iInf.mpr h
    rw [hKrull] at this
    exact hx0 this
  obtain ⟨n, hn, hmin⟩ : ∃ n, x ∉ maximalIdeal L ^ n ∧ ∀ m < n, x ∈ maximalIdeal L ^ m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => by
      have := Nat.find_min hex hm
      simpa using this⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0

  have hxk : x ∈ maximalIdeal L ^ k := hmin k (Nat.lt_succ_self k)
  rw [hτ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hxk
  obtain ⟨u, rfl⟩ := hxk

  have hu : IsUnit u := by
    by_contra hu
    have hum : u ∈ maximalIdeal L := (IsLocalRing.mem_maximalIdeal u).mpr hu
    rw [hτ, Ideal.mem_span_singleton'] at hum
    obtain ⟨v, rfl⟩ := hum
    apply hn
    rw [hτ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨v, by rw [pow_succ]; ring⟩

  obtain ⟨m, hm⟩ := hx
  have hτkm : (τ ^ k) ^ m * u ^ m = 0 := by rw [← hm]; ring
  have hreg' : (τ ^ k) ^ m ∈ nonZeroDivisors L := pow_mem (pow_mem hreg k) m
  have hum0 : u ^ m = 0 := by
    rw [mul_comm] at hτkm
    exact (mem_nonZeroDivisors_iff_right.mp hreg') _ hτkm
  exact (hu.pow m).ne_zero hum0

section Main

variable {A B D₁ : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [Algebra A B] [Module.Flat A B]
  [CommRing D₁] [IsDomain D₁] [Algebra A D₁] [Module.Finite A D₁]

omit [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing B] [Module.Finite A D₁] in

theorem tmul_one_mem_nonZeroDivisors (t : D₁) (ht : t ≠ 0) :
    ((1 : B) ⊗ₜ[A] t) ∈ nonZeroDivisors (B ⊗[A] D₁) := by
  have hinj : Function.Injective (LinearMap.mulRight A t) := fun a b hab => by
    simpa [LinearMap.mulRight_apply, mul_left_injective₀ ht |>.eq_iff] using hab
  have hflat := Module.Flat.lTensor_preserves_injective_linearMap (M := B) (LinearMap.mulRight A t) hinj
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have hmap : ∀ y : B ⊗[A] D₁, LinearMap.lTensor B (LinearMap.mulRight A t) y = y * ((1 : B) ⊗ₜ[A] t) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b d => simp [LinearMap.lTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add y z hy hz => rw [map_add, hy, hz, add_mul]
  apply hflat
  rw [hmap, hx, map_zero]

variable (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
  (hres : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B)

omit [IsLocalRing A] [IsNoetherianRing B] [Module.Flat A B] [IsDomain D₁] [Module.Finite A D₁] in
include hres in

theorem exists_sub_tmul_mem (J : Ideal (B ⊗[A] D₁))
    (hJ : ∀ m ∈ maximalIdeal B, ∀ d : D₁, m ⊗ₜ[A] d ∈ J) (x : B ⊗[A] D₁) :
    ∃ d : D₁, x - (1 : B) ⊗ₜ[A] d ∈ J := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul b d =>
    obtain ⟨a, ha⟩ := hres b
    refine ⟨a • d, ?_⟩
    have : b ⊗ₜ[A] d - (1 : B) ⊗ₜ[A] (a • d) = (b - algebraMap A B a) ⊗ₜ[A] d := by
      rw [TensorProduct.sub_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [this]
    exact hJ _ ha d
  | add x y hx hy =>
    obtain ⟨d₁, h₁⟩ := hx
    obtain ⟨d₂, h₂⟩ := hy
    refine ⟨d₁ + d₂, ?_⟩
    have : x + y - (1 : B) ⊗ₜ[A] (d₁ + d₂) = (x - (1 : B) ⊗ₜ[A] d₁) + (y - (1 : B) ⊗ₜ[A] d₂) := by
      rw [TensorProduct.tmul_add]; abel
    rw [this]
    exact J.add_mem h₁ h₂

include hmax hres in

theorem isReduced_localization_tensor
    (hloc : ∀ 𝔫 : Ideal D₁, 𝔫.IsMaximal → ∃ t ∈ 𝔫, ∀ x ∈ 𝔫, ∃ s ∉ 𝔫, ∃ y : D₁, s * x = t * y)
    (𝔑 : Ideal (B ⊗[A] D₁)) [h𝔑 : 𝔑.IsMaximal] :
    IsReduced (Localization.AtPrime 𝔑) := by
  classical
  set T₁ := B ⊗[A] D₁ with hT₁

  haveI : Module.Finite B T₁ := inferInstance
  haveI : IsNoetherianRing T₁ := Algebra.FiniteType.isNoetherianRing B T₁
  haveI : Algebra.IsIntegral B T₁ := Algebra.IsIntegral.of_finite B T₁

  have ha : 𝔑.comap (algebraMap B T₁) = maximalIdeal B := by
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := B) (S := T₁) 𝔑
    exact IsLocalRing.eq_maximalIdeal this
  have hmB : ∀ m ∈ maximalIdeal B, ∀ d : D₁, m ⊗ₜ[A] d ∈ 𝔑 := by
    intro m hm d
    have h1 : algebraMap B T₁ m ∈ 𝔑 := by
      rw [← Ideal.mem_comap, ha]; exact hm
    have : m ⊗ₜ[A] d = algebraMap B T₁ m * ((1 : B) ⊗ₜ[A] d) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        Algebra.algebraMap_self, RingHom.id_apply]
    rw [this]
    exact 𝔑.mul_mem_right _ h1

  set ι : D₁ →ₐ[A] T₁ := Algebra.TensorProduct.includeRight with hι
  set 𝔫 : Ideal D₁ := 𝔑.comap ι.toRingHom with h𝔫def
  have hιapp : ∀ d : D₁, ι d = (1 : B) ⊗ₜ[A] d := fun d => rfl
  have hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔑).comp ι.toRingHom) := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨d, hd⟩ := exists_sub_tmul_mem hres 𝔑 hmB x
    refine ⟨d, ?_⟩
    rw [RingHom.comp_apply, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hd
  haveI h𝔫max : 𝔫.IsMaximal := by
    have hker : RingHom.ker ((Ideal.Quotient.mk 𝔑).comp ι.toRingHom) = 𝔫 := by
      rw [h𝔫def, ← RingHom.comap_ker, Ideal.mk_ker]
    rw [← hker]
    letI : Field (T₁ ⧸ 𝔑) := Ideal.Quotient.field 𝔑
    exact RingHom.ker_isMaximal_of_surjective _ hsurj

  haveI : Algebra.IsIntegral A D₁ := Algebra.IsIntegral.of_finite A D₁
  have hc : 𝔫.comap (algebraMap A D₁) = maximalIdeal A := by
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) (S := D₁) 𝔫
    exact IsLocalRing.eq_maximalIdeal this
  have hmA : ∀ a ∈ maximalIdeal A, ∀ d : D₁, algebraMap A D₁ a * d ∈ 𝔫 := by
    intro a ha d
    have : algebraMap A D₁ a ∈ 𝔫 := by rw [← Ideal.mem_comap, hc]; exact ha
    exact 𝔫.mul_mem_right _ this

  set 𝔫' : Ideal T₁ := 𝔫.map ι.toRingHom with h𝔫'
  have h𝔫'le : 𝔫' ≤ 𝔑 := Ideal.map_le_iff_le_comap.mpr le_rfl
  have hmB' : ∀ m ∈ maximalIdeal B, ∀ d : D₁, m ⊗ₜ[A] d ∈ 𝔫' := by
    intro m hm d
    rw [← hmax] at hm
    refine Submodule.span_induction (p := fun m _ => ∀ d : D₁, m ⊗ₜ[A] d ∈ 𝔫') ?_ ?_ ?_ ?_ hm d
    · rintro _ ⟨a, ha, rfl⟩ d
      have : (algebraMap A B a) ⊗ₜ[A] d = ι (algebraMap A D₁ a * d) := by
        rw [hιapp, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]
      rw [this]
      exact Ideal.mem_map_of_mem _ (hmA a ha d)
    · intro d; simp
    · intro x y _ _ hx hy d
      rw [TensorProduct.add_tmul]
      exact 𝔫'.add_mem (hx d) (hy d)
    · intro b x _ hx d
      rw [smul_eq_mul, show (b * x) ⊗ₜ[A] d = (b ⊗ₜ[A] (1 : D₁)) * (x ⊗ₜ[A] d) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
      exact 𝔫'.mul_mem_left _ (hx d)
  have hd : 𝔑 = 𝔫' := by
    refine le_antisymm ?_ h𝔫'le
    intro x hx
    obtain ⟨d, hd⟩ := exists_sub_tmul_mem hres 𝔫' hmB' x
    have h1 : (1 : B) ⊗ₜ[A] d ∈ 𝔑 := by
      have := 𝔑.sub_mem hx (h𝔫'le hd)
      simpa using this
    have h2 : d ∈ 𝔫 := by
      rw [h𝔫def, Ideal.mem_comap]
      exact h1
    have h3 : (1 : B) ⊗ₜ[A] d ∈ 𝔫' := by
      rw [← hιapp]
      exact Ideal.mem_map_of_mem _ h2
    have := 𝔫'.add_mem hd h3
    simpa using this

  obtain ⟨t, ht𝔫, hloc𝔫⟩ := hloc 𝔫 h𝔫max
  set Lc := Localization.AtPrime 𝔑 with hLc
  set φ := algebraMap T₁ Lc with hφ
  set τ : Lc := φ ((1 : B) ⊗ₜ[A] t) with hτdef
  have hunit : ∀ s : D₁, s ∉ 𝔫 → IsUnit (φ ((1 : B) ⊗ₜ[A] s)) := by
    intro s hs
    apply IsLocalization.map_units Lc (⟨(1 : B) ⊗ₜ[A] s, ?_⟩ : 𝔑.primeCompl)
    show (1 : B) ⊗ₜ[A] s ∉ 𝔑
    intro h
    apply hs
    rw [h𝔫def, Ideal.mem_comap]
    exact h
  have hmaxL : maximalIdeal Lc = Ideal.span {τ} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal,
      show Ideal.map (algebraMap T₁ Lc) 𝔑 = Ideal.map φ 𝔫' from congrArg _ hd, h𝔫', Ideal.map_map]
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨s, hs, y, hsy⟩ := hloc𝔫 x hx
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      have hφx : (φ.comp ι.toRingHom) x = φ ((1 : B) ⊗ₜ[A] x) := rfl
      rw [hφx]
      obtain ⟨u, hu⟩ := hunit s hs
      refine ⟨φ ((1 : B) ⊗ₜ[A] y) * ↑u⁻¹, ?_⟩
      have key : φ ((1 : B) ⊗ₜ[A] s) * φ ((1 : B) ⊗ₜ[A] x) = τ * φ ((1 : B) ⊗ₜ[A] y) := by
        rw [hτdef, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          hsy]
      rw [← hu] at key
      calc φ ((1 : B) ⊗ₜ[A] y) * ↑u⁻¹ * τ = ↑u⁻¹ * (τ * φ ((1 : B) ⊗ₜ[A] y)) := by ring
        _ = ↑u⁻¹ * (↑u * φ ((1 : B) ⊗ₜ[A] x)) := by rw [key]
        _ = φ ((1 : B) ⊗ₜ[A] x) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ ht𝔫

  have hreg : τ = 0 ∨ τ ∈ nonZeroDivisors Lc := by
    by_cases ht0 : t = 0
    · left
      rw [hτdef, ht0, TensorProduct.tmul_zero, map_zero]
    · right
      have hnzd := tmul_one_mem_nonZeroDivisors (A := A) (B := B) t ht0
      rw [mem_nonZeroDivisors_iff_left]
      intro z hz
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔑.primeCompl z
      rw [hτdef, hφ, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hz
      obtain ⟨m, hm⟩ := hz
      rw [IsLocalization.mk'_eq_zero_iff]
      refine ⟨m, ?_⟩
      rw [← mul_assoc, mul_comm (m : T₁), mul_assoc] at hm
      exact (mem_nonZeroDivisors_iff_left.mp hnzd) _ hm
  haveI : IsNoetherianRing Lc := IsLocalization.isNoetherianRing 𝔑.primeCompl Lc inferInstance
  exact isReduced_of_maximalIdeal_eq_span τ hmaxL hreg

include hmax hres in

theorem isReduced_quotient_map
    (hloc : ∀ 𝔫 : Ideal D₁, 𝔫.IsMaximal → ∃ t ∈ 𝔫, ∀ x ∈ 𝔫, ∃ s ∉ 𝔫, ∃ y : D₁, s * x = t * y)
    (𝔭 : Ideal A) (hker : RingHom.ker (algebraMap A D₁) = 𝔭) :
    IsReduced (B ⧸ 𝔭.map (algebraMap A B)) := by
  classical
  set T₁ := B ⊗[A] D₁ with hT₁
  haveI hT : IsReduced T₁ :=
    isReduced_ofLocalizationMaximal T₁ (fun J hJ => isReduced_localization_tensor hmax hres hloc J)

  have hle : 𝔭.map (algebraMap A B) ≤ RingHom.ker (algebraMap B T₁) := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    have hp0 : algebraMap A D₁ p = 0 := by rw [← RingHom.mem_ker, hker]; exact hp
    rw [Ideal.mem_comap, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply,
      Algebra.TensorProduct.algebraMap_apply', hp0, TensorProduct.tmul_zero]
  set f : B ⧸ 𝔭.map (algebraMap A B) →+* T₁ :=
    Ideal.Quotient.lift (𝔭.map (algebraMap A B)) (algebraMap B T₁) (fun x hx => hle hx) with hf

  have hῑ : ∀ a ∈ 𝔭, Algebra.ofId A D₁ a = 0 := fun a ha => by
    rw [Algebra.ofId_apply, ← RingHom.mem_ker, hker]; exact ha
  set ῑ : (A ⧸ 𝔭) →ₐ[A] D₁ := Ideal.Quotient.liftₐ 𝔭 (Algebra.ofId A D₁) hῑ with hῑdef
  have hῑinj : Function.Injective ῑ := by
    rw [hῑdef]
    show Function.Injective (Ideal.Quotient.lift 𝔭 ((Algebra.ofId A D₁ : A →ₐ[A] D₁) : A →+* D₁) hῑ)
    rw [Ideal.injective_lift_iff]
    exact hker
  have hg : Function.Injective (LinearMap.lTensor B ῑ.toLinearMap) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hῑinj
  set e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B 𝔭 with he
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hf, Ideal.Quotient.lift_mk] at hx

    have h1 : LinearMap.lTensor B ῑ.toLinearMap (e (Ideal.Quotient.mk _ b)) = algebraMap B T₁ b := by
      rw [he, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply,
        map_one, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [hx, ← (LinearMap.lTensor B ῑ.toLinearMap).map_zero] at h1
    have h2 := hg h1
    rw [← e.map_zero] at h2
    exact e.injective h2
  exact isReduced_of_injective f hfinj

end Main

end R1AF8H1

open IsLocalRing in
theorem solution
    {A B D₁ : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra A B] [Module.Flat A B]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B)
    (hres : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ IsLocalRing.maximalIdeal B)
    [CommRing D₁] [IsDomain D₁] [Algebra A D₁] [Module.Finite A D₁]
    (hloc : ∀ 𝔫 : Ideal D₁, 𝔫.IsMaximal → ∃ t ∈ 𝔫, ∀ x ∈ 𝔫, ∃ s ∉ 𝔫, ∃ y : D₁, s * x = t * y)
    (𝔭 : Ideal A) (hker : RingHom.ker (algebraMap A D₁) = 𝔭) :
    IsReduced (B ⧸ 𝔭.map (algebraMap A B)) :=
  R1AF8H1.isReduced_quotient_map hmax hres hloc 𝔭 hker

end S_IsLocalRing_isReduced_quotient_map_of_flat_of_locallyPrincipalOverring
end P2MW
export P2MW.S_IsLocalRing_isReduced_quotient_map_of_flat_of_locallyPrincipalOverring (solution)
