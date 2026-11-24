-- Prove2me | solution 1 for GlobalTheory.RowLev.PrimeIdem.exists_idem_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:15:39.738421+00:00
-- url     : https://prove2.me/submissions/1612a025-7040-4f43-8c14-8364a2b89dee

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_prime
import Theorems.Thm_GlobalTheory_RowLev_Red_map_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
open GlobalTheory.RowLev.PrimeIdem
namespace GlobalTheory.RowLev.PrimeIdem
theorem _root_.solution {B R : Type} [CommRing B] [IsDedekindDomain B] [CommRing R] (ψ : B →+* R) (g : B)
    (hg : g ≠ 0) (e : R) (he : e * e = e)
    (hH : ∀ a : R, a * a - a ∈ Ideal.span {ψ g} → ∃ x, e * (a + ψ g * x) * (e * (a + ψ g * x)) = e * (a + ψ g * x))
    (hJ : ∀ r : R, ∃ s, e * (1 - ψ g * r) * s = e) (happ : ∀ z : R, ∃ b t, z = ψ b + ψ g * t)
    (w : HeightOneSpectrum B) (hgw : g ∈ w.asIdeal) (hew : 1 - e ∈ w.asIdeal.map ψ) :
    ∃ ε : R, ε * ε = ε ∧ e * ε = ε ∧ 1 - ε ∈ w.asIdeal.map ψ ∧
      (∀ u : HeightOneSpectrum B, u ≠ w → g ∈ u.asIdeal → ε ∈ u.asIdeal.map ψ) ∧
      (∀ z : R, z ∉ w.asIdeal.map ψ → ∃ t, z * t * ε = ε) ∧
      ∀ η ∈ w.asIdeal.map ψ, η * η = η → ε * η = 0 := by
  have h0 : Ideal.span {g} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hg
  obtain ⟨k, c, hc, hk⟩ := WfDvdMonoid.max_power_factor h0 w.irreducible
  have hwm := w.isMaximal
  have hcop : IsCoprime w.asIdeal c := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    exact hc (Ideal.dvd_iff_le.2 (le_sup_right.trans (hwm.eq_of_le hne le_sup_left).ge))
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hc
    rw [pow_zero, one_mul] at hk
    rw [← hk]; exact Ideal.dvd_span_singleton.2 hgw
  obtain ⟨a', ha', a, ha, haa⟩ := Ideal.isCoprime_iff_exists.1 (hcop.pow_left (m := k))
  have hmul : ∀ x ∈ (w.asIdeal ^ k).map ψ, ∀ y ∈ c.map ψ, ∃ r, x * y = ψ g * r := fun x hx y hy => by
    have := Ideal.mul_mem_mul hx hy
    rw [← Ideal.map_mul, ← hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at this
    exact this
  have hgc : g ∈ c := Ideal.dvd_span_singleton.1 (hk ▸ Dvd.intro_left _ rfl)
  have haa' : ψ a' = 1 - ψ a := by rw [← map_one ψ, ← haa, map_add]; ring
  obtain ⟨x, hx⟩ := hH (ψ a) (by
    obtain ⟨r, hr⟩ := hmul _ (Ideal.mem_map_of_mem ψ ha') _ (Ideal.mem_map_of_mem ψ ha)
    rw [Ideal.mem_span_singleton]
    exact ⟨-r, by rw [haa'] at hr; linear_combination -hr⟩)
  set ε := e * (ψ a + ψ g * x) with hε
  have heε : e * ε = ε := by rw [hε, ← mul_assoc, he]
  have hεc : ε ∈ c.map ψ := Ideal.mul_mem_left _ _
    (add_mem (Ideal.mem_map_of_mem ψ ha) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem ψ hgc)))
  have hgw' := Ideal.mem_map_of_mem ψ hgw
  refine ⟨ε, hx, heε, ?_, fun u hu hgu => ?_, fun z hz => ?_, fun η hη hηη => ?_⟩
  · have : 1 - ε = (1 - e) + e * ψ a' - e * x * ψ g := by rw [haa', hε]; ring
    rw [this]
    exact sub_mem (add_mem hew (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem ψ (Ideal.pow_le_self hk0 ha'))))
      (Ideal.mul_mem_left _ _ hgw')
  · refine Ideal.map_mono ?_ hεc
    have h1 : u.asIdeal ∣ w.asIdeal ^ k * c := hk ▸ Ideal.dvd_span_singleton.2 hgu
    rcases u.prime.dvd_or_dvd h1 with h | h
    · exact absurd (HeightOneSpectrum.ext (hwm.eq_of_le u.isPrime.ne_top
        (Ideal.le_of_dvd (u.prime.dvd_of_dvd_pow h))).symm) hu
    · exact Ideal.le_of_dvd h
  · obtain ⟨b, t, rfl⟩ := happ z
    have hb : b ∉ w.asIdeal := fun h =>
      hz (add_mem (Ideal.mem_map_of_mem ψ h) (Ideal.mul_mem_right _ _ hgw'))
    have hcb : IsCoprime w.asIdeal (Ideal.span {b}) := by
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      exact hb ((le_sup_right.trans (hwm.eq_of_le hne le_sup_left).ge) (Ideal.mem_span_singleton_self b))
    obtain ⟨d, hd, d', hd', hdd⟩ := Ideal.isCoprime_iff_exists.1 (hcb.pow_left (m := k))
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.1 hd'
    have hdd' : ψ d = 1 - ψ b * ψ q := by rw [← map_one ψ, ← hdd, map_add, map_mul]; ring
    obtain ⟨r, hr⟩ := hmul _ (Ideal.mem_map_of_mem ψ hd) _ hεc
    obtain ⟨s, hs⟩ := hJ (r - t * ψ q * ε)
    rw [hdd'] at hr
    refine ⟨ψ q * s, ?_⟩
    linear_combination ε * hs + (1 - (1 - ψ g * (r - t * ψ q * ε)) * s) * heε - s * ε * hr
      + s * (1 - (ψ b + ψ g * t) * ψ q) * hx
  · have hi : IsIdempotentElem η := hηη
    have h1 : η ∈ (w.asIdeal ^ k).map ψ := by
      rw [Ideal.map_pow, ← hi.pow_eq hk0]; exact Ideal.pow_mem_pow hη k
    obtain ⟨r, hr⟩ := hmul _ h1 _ hεc
    obtain ⟨s, hs⟩ := hJ r
    rw [← hr] at hs
    linear_combination -η * ε * hs - η * heε - e * s * η * η * hx - e * s * ε * hηη
end GlobalTheory.RowLev.PrimeIdem
