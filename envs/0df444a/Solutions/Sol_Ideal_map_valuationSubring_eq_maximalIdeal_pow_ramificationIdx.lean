-- Prove2me | solution 1 for Ideal.map_valuationSubring_eq_maximalIdeal_pow_ramificationIdx
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/9237a5ab-cfbc-563c-96f6-315b4ea35ae3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_map_valuationSubring_eq_maximalIdeal_pow_ramificationIdx

set_option autoImplicit false

open IsLocalRing

theorem solution
    {R S F : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S] [Field F]
    [Algebra R S] [Module.IsTorsionFree R S] [Algebra S F] [IsFractionRing S F]
    (p : Ideal R) (hp : p ≠ ⊥) (𝔓 : Ideal S) [𝔓.IsMaximal] [𝔓.LiesOver p]
    (P : ValuationSubring F)
    (hSP : ∀ s : S, algebraMap S F s ∈ P)
    (hcent : ∀ s : S, algebraMap S F s ∈ P.nonunits ↔ s ∈ 𝔓)
    (hfrac : ∀ e : ↥P, ∃ s t : S, t ∉ 𝔓 ∧ (e : F) * algebraMap S F t = algebraMap S F s)
    (φ : R →+* ↥P) (hφ : ∀ r : R, ((φ r : ↥P) : F) = algebraMap S F (algebraMap R S r)) :
    Ideal.map φ p = IsLocalRing.maximalIdeal ↥P ^ Ideal.ramificationIdx' p 𝔓 := by
  classical

  let ψ : S →+* ↥P := (algebraMap S F).codRestrict P hSP
  have hψ : ∀ s : S, ((ψ s : ↥P) : F) = algebraMap S F s := fun s => rfl
  letI algSP : Algebra S ↥P := ψ.toAlgebra
  letI algRP : Algebra R ↥P := φ.toAlgebra
  haveI : IsScalarTower R S ↥P := IsScalarTower.of_algebraMap_eq fun r => by
    apply Subtype.ext
    change ((φ r : ↥P) : F) = ((ψ (algebraMap R S r) : ↥P) : F)
    rw [hψ, hφ]

  have hunit : ∀ {t : S}, t ∉ 𝔓 → IsUnit (ψ t) := by
    intro t ht
    by_contra h
    have : (ψ t : ↥P) ∈ maximalIdeal ↥P := h
    rw [← P.coe_mem_nonunits_iff, hψ] at this
    exact ht ((hcent t).mp this)

  haveI : IsLocalization.AtPrime ↥P 𝔓 := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨t, ht⟩
      exact hunit ht
    · intro e
      obtain ⟨s, t, ht, hst⟩ := hfrac e
      refine ⟨⟨s, ⟨t, ht⟩⟩, Subtype.ext ?_⟩
      change (e : F) * ((ψ t : ↥P) : F) = ((ψ s : ↥P) : F)
      rw [hψ, hψ]; exact hst
    · intro s₁ s₂ h
      have h' : algebraMap S F s₁ = algebraMap S F s₂ := congrArg (fun x : ↥P => (x : F)) h
      exact ⟨1, by simpa using IsFractionRing.injective S F h'⟩
  have h𝔓0 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝔓
  haveI : IsDiscreteValuationRing ↥P :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S h𝔓0 ↥P

  have hmap𝔓 : Ideal.map (algebraMap S ↥P) 𝔓 = maximalIdeal ↥P :=
    IsLocalization.AtPrime.map_eq_maximalIdeal 𝔓 ↥P
  have hm0 : maximalIdeal ↥P ≠ ⊥ := IsDiscreteValuationRing.not_a_field ↥P
  have he1 : Ideal.ramificationIdx' 𝔓 (maximalIdeal ↥P) = 1 := by
    apply Ideal.ramificationIdx_spec
    · rw [pow_one, hmap𝔓]
    · rw [hmap𝔓]
      intro hle
      have hlt := Ideal.pow_succ_lt_pow hm0 1
      rw [pow_one] at hlt
      exact (lt_irrefl _) (lt_of_le_of_lt hle hlt)

  have hψinj : Function.Injective (algebraMap S ↥P) := by
    intro a b h
    exact IsFractionRing.injective S F (congrArg (fun x : ↥P => (x : F)) h)
  have hpS : Ideal.map (algebraMap R S) p ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp
  have hfg : Ideal.map (algebraMap R ↥P) p ≠ ⊥ := by
    rw [IsScalarTower.algebraMap_eq R S ↥P, ← Ideal.map_map]
    exact fun h => hpS ((Ideal.map_eq_bot_iff_of_injective hψinj).mp h)
  have hg0 : Ideal.map (algebraMap S ↥P) 𝔓 ≠ ⊥ := by rw [hmap𝔓]; exact hm0
  have hg : Ideal.map (algebraMap S ↥P) 𝔓 ≤ maximalIdeal ↥P := hmap𝔓.le
  have htower := Ideal.ramificationIdx_algebra_tower (p := p) (P := 𝔓) (Q := maximalIdeal ↥P) hg0 hfg hg
  rw [he1, mul_one] at htower

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥P
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hfg hϖ
  have hmax : maximalIdeal ↥P = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hn' : Ideal.map (algebraMap R ↥P) p = maximalIdeal ↥P ^ n := by
    rw [hn, hmax, Ideal.span_singleton_pow]
  have hidx : Ideal.ramificationIdx' p (maximalIdeal ↥P) = n := by
    apply Ideal.ramificationIdx_spec
    · exact hn'.le
    · rw [hn']
      intro hle
      exact (lt_irrefl _) (lt_of_le_of_lt hle (Ideal.pow_succ_lt_pow hm0 n))
  change Ideal.map (algebraMap R ↥P) p = _
  rw [hn', ← htower, hidx]

end S_Ideal_map_valuationSubring_eq_maximalIdeal_pow_ramificationIdx
end P2MW
export P2MW.S_Ideal_map_valuationSubring_eq_maximalIdeal_pow_ramificationIdx (solution)
