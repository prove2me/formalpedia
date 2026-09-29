-- Prove2me | solution 1 for IsDiscreteValuationRing.forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c218c309-c0d2-5a52-b0bc-6a742f8544df

import Mathlib
import Theorems.Thm_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace TotRamPackage

theorem mem_of_isIntegral {O E : Type*} [CommRing O] [Field E] [Algebra O E]
    (V : ValuationSubring E) (hOV : ∀ x : O, algebraMap O E x ∈ V)
    {y : E} (hy : IsIntegral O y) : y ∈ V := by
  let φ : O →+* ↥V := (algebraMap O E).codRestrict V.toSubring hOV
  have hy' : IsIntegral ↥V y := by
    obtain ⟨q, hq, hqy⟩ := hy
    refine ⟨q.map φ, hq.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hqy
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := E)).mp hy'
  rw [← hz]
  exact z.2

theorem not_mem_nonunits_of_isUnit {O E : Type*} [CommRing O] [Field E] [Algebra O E]
    (V : ValuationSubring E) (hOV : ∀ x : O, algebraMap O E x ∈ V) {x : O} (hx : IsUnit x) :
    algebraMap O E x ∉ V.nonunits := by
  obtain ⟨u, rfl⟩ := hx
  intro hmem
  have hunit : IsUnit (⟨algebraMap O E ↑u, hOV ↑u⟩ : ↥V) :=
    (Units.map ((algebraMap O E).codRestrict V.toSubring hOV : O →* ↥V) u).isUnit
  have hmem' := (ValuationSubring.coe_mem_nonunits_iff (a := ⟨algebraMap O E ↑u, hOV ↑u⟩)).mp hmem
  exact (IsLocalRing.mem_maximalIdeal _ |>.mp hmem') hunit

theorem inv_not_mem_of_mem_nonunits {E : Type*} [Field E] (V : ValuationSubring E) {x : E}
    (hx : x ∈ V.nonunits) (hx0 : x ≠ 0) : x⁻¹ ∉ V := by
  intro hinv
  rw [ValuationSubring.mem_nonunits_iff] at hx
  have hle : V.valuation x⁻¹ ≤ 1 := (V.valuation_le_one_iff _).mpr hinv
  have : V.valuation (x * x⁻¹) < 1 := by
    rw [map_mul]
    calc V.valuation x * V.valuation x⁻¹ ≤ V.valuation x * 1 := mul_le_mul_right hle _
      _ < 1 := by rw [mul_one]; exact hx
  rw [mul_inv_cancel₀ hx0, map_one] at this
  exact lt_irrefl _ this

end TotRamPackage

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
open TotRamPackage in
theorem solution
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (E : Type*) [Field E] [Algebra O E]
    [IsDedekindDomain ↥(integralClosure O E)] [Module.Finite O ↥(integralClosure O E)]
    [IsFractionRing ↥(integralClosure O E) E]
    (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ)
    (𝔓 : Ideal ↥(integralClosure O E)) [h𝔓 : 𝔓.IsPrime] (h0 : 𝔓 ≠ ⊥)
    (hover : (IsLocalRing.maximalIdeal O).primesOver ↥(integralClosure O E) = {𝔓})
    (he : (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓 = n)
    (hf : (IsLocalRing.maximalIdeal O).inertiaDeg' 𝔓 = 1)
    (W : ValuationSubring E)
    (hW : W = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E ⟨𝔓, h𝔓, h0⟩) :
    (∀ W₁ W₂ : ValuationSubring E,
        (∀ x : O, algebraMap O E x ∈ W₁) → (∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O E x ∈ W₁.nonunits) →
        (∀ x : O, algebraMap O E x ∈ W₂) → (∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O E x ∈ W₂.nonunits) →
        W₁ = W₂) ∧
    (∀ x : O, algebraMap O E x ∈ W) ∧
    (∀ x : O, algebraMap O E x ∈ W.nonunits ↔ x ∈ IsLocalRing.maximalIdeal O) ∧
    (∀ e : ↥W, ∃ f : O, (e : E) - algebraMap O E f ∈ W.nonunits) ∧
    (∃ (π : ↥W) (v : (↥W)ˣ), Irreducible π ∧
      algebraMap O E ϖ = ((v : ↥W) : E) * ((π : ↥W) : E) ^ n) := by
  classical
  set p := IsLocalRing.maximalIdeal O with hpdef
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field O

  have h𝔓mem : 𝔓 ∈ p.primesOver ↥(integralClosure O E) := by
    rw [hover]
    exact Set.mem_singleton 𝔓
  haveI h𝔓over : 𝔓.LiesOver p := h𝔓mem.2
  have honly : ∀ (Q : Ideal ↥(integralClosure O E)), Q.IsPrime → Q.LiesOver p → Q = 𝔓 := fun Q hQ hQo => by
    have hQ' : Q ∈ p.primesOver ↥(integralClosure O E) := ⟨hQ, hQo⟩
    rw [hover] at hQ'
    exact hQ'

  have hinjR : Function.Injective (algebraMap O ↥(integralClosure O E)) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hker
    have hprime : (RingHom.ker (algebraMap O ↥(integralClosure O E))).IsPrime := RingHom.ker_isPrime _
    have hkp : RingHom.ker (algebraMap O ↥(integralClosure O E)) = p := by
      obtain ⟨-, P, -, hPuniq⟩ := (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime O).mp inferInstance
      rw [hPuniq _ ⟨hker, hprime⟩, hPuniq p ⟨hp0, inferInstance⟩]
    have hbot : (⊥ : Ideal ↥(integralClosure O E)).LiesOver p := ⟨by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, hkp]⟩
    exact h0 (honly ⊥ Ideal.isPrime_bot hbot).symm
  have hinjE : Function.Injective (algebraMap O E) := by
    rw [IsScalarTower.algebraMap_eq O ↥(integralClosure O E) E]
    exact (IsFractionRing.injective ↥(integralClosure O E) E).comp hinjR
  haveI : FaithfulSMul O ↥(integralClosure O E) := (faithfulSMul_iff_algebraMap_injective O ↥(integralClosure O E)).mpr hinjR
  haveI : Module.IsTorsionFree O ↥(integralClosure O E) := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  have hmap0 : Ideal.map (algebraMap O ↥(integralClosure O E)) p ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective hinjR).not.mpr hp0

  generalize hvP : (⟨𝔓, h𝔓, h0⟩ : IsDedekindDomain.HeightOneSpectrum ↥(integralClosure O E)) = vP at hW
  have hvPI : vP.asIdeal = 𝔓 := by rw [← hvP]
  subst hW
  haveI hloc : IsLocalization.AtPrime ↥(vP.valuationSubringAtPrime E) vP.asIdeal := inferInstance
  haveI : IsDiscreteValuationRing ↥(vP.valuationSubringAtPrime E) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ↥(integralClosure O E) vP.ne_bot
      ↥(vP.valuationSubringAtPrime E)
  have hcoeRW : ∀ r : ↥(integralClosure O E), ((algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E) r : ↥(vP.valuationSubringAtPrime E)) : E) = algebraMap ↥(integralClosure O E) E r := fun _ => rfl
  have hRW : ∀ r : ↥(integralClosure O E), algebraMap ↥(integralClosure O E) E r ∈ (vP.valuationSubringAtPrime E) := fun r => by
    rw [← hcoeRW]
    exact (algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E) r).2
  have hOW : ∀ x : O, algebraMap O E x ∈ (vP.valuationSubringAtPrime E) := fun x => by
    rw [IsScalarTower.algebraMap_apply O ↥(integralClosure O E) E]
    exact hRW _
  have hcomapW : (IsLocalRing.maximalIdeal ↥(vP.valuationSubringAtPrime E)).comap (algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E)) = 𝔓 :=
    (IsLocalization.AtPrime.comap_maximalIdeal ↥(vP.valuationSubringAtPrime E) vP.asIdeal).trans hvPI
  have hRnon : ∀ r : ↥(integralClosure O E), algebraMap ↥(integralClosure O E) E r ∈ (vP.valuationSubringAtPrime E).nonunits ↔ r ∈ 𝔓 := fun r => by
    rw [← hcoeRW, ValuationSubring.coe_mem_nonunits_iff, ← Ideal.mem_comap, hcomapW]

  have hmW : ∀ x : O, algebraMap O E x ∈ (vP.valuationSubringAtPrime E).nonunits ↔ x ∈ p := fun x => by
    constructor
    · intro hx
      by_contra hx'
      exact not_mem_nonunits_of_isUnit (vP.valuationSubringAtPrime E) hOW ((IsLocalRing.notMem_maximalIdeal).mp hx') hx
    · intro hx
      rw [IsScalarTower.algebraMap_apply O ↥(integralClosure O E) E, hRnon]
      exact (Ideal.mem_of_liesOver 𝔓 p x).mp hx

  have huniq : ∀ W₁ : ValuationSubring E, (∀ x : O, algebraMap O E x ∈ W₁) →
      (∀ x ∈ p, algebraMap O E x ∈ W₁.nonunits) → W₁ = (vP.valuationSubringAtPrime E) := by
    intro W₁ hOW₁ hdom₁
    have hRW₁ : ∀ r : ↥(integralClosure O E), algebraMap ↥(integralClosure O E) E r ∈ W₁ := fun r => mem_of_isIntegral W₁ hOW₁ r.2
    have hϖp : ϖ ∈ p := by
      rw [hpdef, hϖ.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self ϖ
    have hϖ₁ : algebraMap O E ϖ ∈ W₁.nonunits := hdom₁ ϖ hϖp
    have hϖE : algebraMap O E ϖ ≠ 0 := (map_ne_zero_iff _ hinjE).mpr hϖ.ne_zero
    have hW₁top : W₁ ≠ ⊤ := by
      intro htop
      apply inv_not_mem_of_mem_nonunits W₁ hϖ₁ hϖE
      rw [htop]
      exact ValuationSubring.mem_top _
    obtain ⟨v₁, hv₁, hv₁mem⟩ :=
      ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem W₁ hRW₁ hW₁top
    have hlies : v₁.asIdeal.LiesOver p := by
      refine ⟨Ideal.ext fun x => ?_⟩
      rw [Ideal.under_def, Ideal.mem_comap, hv₁mem, ← IsScalarTower.algebraMap_apply O ↥(integralClosure O E) E]
      constructor
      · exact hdom₁ x
      · intro hx
        by_contra hx'
        exact not_mem_nonunits_of_isUnit W₁ hOW₁ ((IsLocalRing.notMem_maximalIdeal).mp hx') hx
    have hv₁𝔓 : v₁.asIdeal = 𝔓 := honly v₁.asIdeal v₁.isPrime hlies
    have hvv : v₁ = vP := IsDedekindDomain.HeightOneSpectrum.ext (hv₁𝔓.trans hvPI.symm)
    rw [hv₁, hvv]

  haveI h𝔓max : 𝔓.IsMaximal := h𝔓.isMaximal h0
  letI hfldp : Field (O ⧸ p) := Ideal.Quotient.field p
  letI hfld𝔓 : Field (↥(integralClosure O E) ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  have hres𝔓 : ∀ r : ↥(integralClosure O E), ∃ c : O, r - algebraMap O ↥(integralClosure O E) c ∈ 𝔓 := by
    intro r
    have h1 := hf
    rw [Ideal.inertiaDeg_algebraMap] at h1
    have h1' : Module.finrank (O ⧸ p) (↥(integralClosure O E) ⧸ 𝔓) = 1 := by convert h1
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : ↥(integralClosure O E) ⧸ 𝔓) one_ne_zero).mp h1'
      (Ideal.Quotient.mk 𝔓 r)
    obtain ⟨c₀, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨c₀, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, ← hc, Algebra.smul_def, mul_one,
      Ideal.Quotient.mk_algebraMap, IsScalarTower.algebraMap_apply O (O ⧸ p) (↥(integralClosure O E) ⧸ 𝔓) c₀,
      Ideal.Quotient.algebraMap_eq]
  have hres : ∀ e : ↥(vP.valuationSubringAtPrime E), ∃ f : O, (e : E) - algebraMap O E f ∈ (vP.valuationSubringAtPrime E).nonunits := by
    intro e
    obtain ⟨⟨a, s⟩, hmk⟩ := IsLocalization.mk'_surjective vP.asIdeal.primeCompl e

    have hs : (s : ↥(integralClosure O E)) ∉ 𝔓 := fun h => s.2 (hvPI.symm ▸ h)
    have hs0 : Ideal.Quotient.mk 𝔓 (s : ↥(integralClosure O E)) ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective ((Ideal.Quotient.mk 𝔓 (s : ↥(integralClosure O E)))⁻¹)
    have hst : (s : ↥(integralClosure O E)) * t - 1 ∈ 𝔓 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ht, mul_inv_cancel₀ hs0, map_one, sub_self]
    obtain ⟨c, hc⟩ := hres𝔓 (a * t)
    refine ⟨c, ?_⟩

    have hasc : a - (s : ↥(integralClosure O E)) * algebraMap O ↥(integralClosure O E) c ∈ 𝔓 := by
      have : a - (s : ↥(integralClosure O E)) * algebraMap O ↥(integralClosure O E) c
          = -(a * ((s : ↥(integralClosure O E)) * t - 1)) + (s : ↥(integralClosure O E)) * (a * t - algebraMap O ↥(integralClosure O E) c) := by ring
      rw [this]
      exact 𝔓.add_mem (𝔓.neg_mem (Ideal.mul_mem_left _ _ hst)) (Ideal.mul_mem_left _ _ hc)

    have hsW : IsUnit (algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E) (s : ↥(integralClosure O E))) := IsLocalization.map_units ↥(vP.valuationSubringAtPrime E) s
    have hmem : algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E) (s : ↥(integralClosure O E)) * (e - algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E) (algebraMap O ↥(integralClosure O E) c)) ∈
        IsLocalRing.maximalIdeal ↥(vP.valuationSubringAtPrime E) := by
      have h2 : algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E) (a - (s : ↥(integralClosure O E)) * algebraMap O ↥(integralClosure O E) c) ∈ IsLocalRing.maximalIdeal ↥(vP.valuationSubringAtPrime E) := by
        rw [← Ideal.mem_comap, hcomapW]
        exact hasc
      have h3 : algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E) (s : ↥(integralClosure O E)) * e = algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E) a := by
        rw [← hmk, mul_comm]
        exact IsLocalization.mk'_spec ↥(vP.valuationSubringAtPrime E) a s
      rw [mul_sub, h3, ← map_mul, ← map_sub]
      exact h2
    have hmem' : e - algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E) (algebraMap O ↥(integralClosure O E) c) ∈ IsLocalRing.maximalIdeal ↥(vP.valuationSubringAtPrime E) :=
      ((Ideal.IsPrime.mem_or_mem inferInstance hmem).resolve_left
        fun h => (IsLocalRing.mem_maximalIdeal _ |>.mp h) hsW)
    rw [← ValuationSubring.coe_mem_nonunits_iff] at hmem'
    have hcoe : (((e - algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E) (algebraMap O ↥(integralClosure O E) c) : ↥(vP.valuationSubringAtPrime E))) : E)
        = (e : E) - algebraMap O E c := by
      rw [IsScalarTower.algebraMap_apply O ↥(integralClosure O E) E, ← hcoeRW]
      rfl
    rw [hcoe] at hmem'
    exact hmem'

  have hmapO : Ideal.map (algebraMap O ↥(integralClosure O E)) p = 𝔓 ^ n := by
    have hall : ∀ Q ∈ UniqueFactorizationMonoid.factors (Ideal.map (algebraMap O ↥(integralClosure O E)) p), Q = 𝔓 := by
      intro Q hQ
      have hQ' : Q ∈ IsDedekindDomain.primesOverFinset p ↥(integralClosure O E) := Multiset.mem_toFinset.mpr hQ
      obtain ⟨hQp, hQo⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 ↥(integralClosure O E)).mp hQ'
      exact honly Q hQp hQo
    have hcount : (UniqueFactorizationMonoid.factors (Ideal.map (algebraMap O ↥(integralClosure O E)) p)).count 𝔓 = n := by
      rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_factors_count hmap0 h𝔓 h0, he]
    have hcard : Multiset.card (UniqueFactorizationMonoid.factors (Ideal.map (algebraMap O ↥(integralClosure O E)) p)) = n := by
      have h := hcount
      rw [Multiset.eq_replicate_of_mem hall, Multiset.count_replicate_self] at h
      exact h
    have hprod := UniqueFactorizationMonoid.factors_prod hmap0
    rw [Multiset.eq_replicate_of_mem hall, hcard, Multiset.prod_replicate] at hprod
    exact (associated_iff_eq.mp hprod).symm
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(vP.valuationSubringAtPrime E)
  have hmaxW : IsLocalRing.maximalIdeal ↥(vP.valuationSubringAtPrime E) = Ideal.span {π} := hπ.maximalIdeal_eq
  have hspan : Ideal.span {((algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E)).comp (algebraMap O ↥(integralClosure O E))) ϖ} = Ideal.span {π ^ n} := by
    have h1 : Ideal.map ((algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E)).comp (algebraMap O ↥(integralClosure O E))) p
        = Ideal.span {((algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E)).comp (algebraMap O ↥(integralClosure O E))) ϖ} := by
      rw [hpdef, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    rw [← h1, ← Ideal.map_map, hmapO, ← hvPI, Ideal.map_pow,
      IsLocalization.AtPrime.map_eq_maximalIdeal vP.asIdeal ↥(vP.valuationSubringAtPrime E), hmaxW, Ideal.span_singleton_pow]
  obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hram : ∃ (π : ↥(vP.valuationSubringAtPrime E)) (v : (↥(vP.valuationSubringAtPrime E))ˣ), Irreducible π ∧
      algebraMap O E ϖ = ((v : ↥(vP.valuationSubringAtPrime E)) : E) * ((π : ↥(vP.valuationSubringAtPrime E)) : E) ^ n := by
    refine ⟨π, w⁻¹, hπ, ?_⟩
    have h2 : ((algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E)).comp (algebraMap O ↥(integralClosure O E))) ϖ = π ^ n * ↑w⁻¹ := by
      rw [← hw, mul_assoc, Units.mul_inv, mul_one]
    have hcoe : algebraMap O E ϖ = ((((algebraMap ↥(integralClosure O E) ↥(vP.valuationSubringAtPrime E)).comp (algebraMap O ↥(integralClosure O E))) ϖ : ↥(vP.valuationSubringAtPrime E)) : E) := by
      rw [RingHom.comp_apply, hcoeRW, ← IsScalarTower.algebraMap_apply]
    rw [hcoe, h2, MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_comm]
  exact ⟨fun W₁ W₂ h₁ h₁' h₂ h₂' => (huniq W₁ h₁ h₁').trans (huniq W₂ h₂ h₂').symm, hOW, hmW, hres, hram⟩

end S_IsDiscreteValuationRing_forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton
end P2MW
export P2MW.S_IsDiscreteValuationRing_forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton (solution)
