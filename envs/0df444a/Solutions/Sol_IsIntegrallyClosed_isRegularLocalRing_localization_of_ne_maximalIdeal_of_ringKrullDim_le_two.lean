-- Prove2me | solution 1 for IsIntegrallyClosed.isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f117ebe0-85ac-599d-a4e1-7e1f7de5c212

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two

set_option autoImplicit false

theorem solution
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsLocalRing R₀] [IsIntegrallyClosed R₀]
    (hdim : ringKrullDim R₀ ≤ (2 : WithBot ℕ∞))
    (𝔯 : Ideal R₀) [𝔯.IsPrime] (h𝔯 : 𝔯 ≠ IsLocalRing.maximalIdeal R₀) :
    IsRegularLocalRing (Localization.AtPrime 𝔯) := by
  classical
  set A := Localization.AtPrime 𝔯

  have hlt : 𝔯 < IsLocalRing.maximalIdeal R₀ :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) h𝔯
  have h1 : 𝔯.height + 1 ≤ (IsLocalRing.maximalIdeal R₀).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hm : (IsLocalRing.maximalIdeal R₀).height ≤ 2 := by
    have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R₀)
    rw [← h2] at hdim
    exact WithBot.coe_le_coe.mp hdim
  have hrh : 𝔯.height ≤ 1 := by
    have h3 : 𝔯.height + 1 ≤ 2 := h1.trans hm
    have hne : 𝔯.height ≠ ⊤ := by
      intro htop; rw [htop] at h3; exact absurd h3 (by decide)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hn] at h3 ⊢
    have : (n : ℕ∞) + 1 = ((n + 1 : ℕ) : ℕ∞) := by push_cast; rfl
    rw [this] at h3
    have h4 : n + 1 ≤ 2 := by exact_mod_cast h3
    exact_mod_cast (by omega : n ≤ 1)
  have hdimA : ringKrullDim A ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔯 A]
    exact_mod_cast hrh
  haveI hic : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_isLocalization A 𝔯.primeCompl (Ideal.primeCompl_le_nonZeroDivisors 𝔯)
  by_cases hF : IsField A
  · letI : Field A := hF.toField
    infer_instance
  ·
    haveI : Ring.DimensionLEOne A := by
      refine ⟨fun {p} hp0 hp => ?_⟩
      haveI : p.IsPrime := hp
      have hb : (⊥ : Ideal A) < p := bot_lt_iff_ne_bot.mpr hp0
      have hh : (⊥ : Ideal A).height + 1 ≤ p.height := Ideal.height_add_one_le_of_lt_of_isPrime hb
      rw [Ideal.height_bot, zero_add] at hh
      have hle : (p.height : WithBot ℕ∞) ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_isPrime
      have hge : (1 : WithBot ℕ∞) ≤ p.height := by exact_mod_cast hh
      exact Ideal.isMaximal_of_height_eq_ringKrullDim (le_antisymm hle (hdimA.trans hge))
    haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing 𝔯.primeCompl A inferInstance
    have hded : IsDedekindDomain A := { }
    haveI : IsDiscreteValuationRing A := ((IsDiscreteValuationRing.TFAE A hF).out 0 2).mpr hded
    infer_instance

end S_IsIntegrallyClosed_isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two
end P2MW
export P2MW.S_IsIntegrallyClosed_isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two (solution)
