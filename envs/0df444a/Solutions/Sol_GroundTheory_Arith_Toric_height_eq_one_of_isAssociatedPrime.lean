-- Prove2me | solution 1 for GroundTheory.Arith.Toric.height_eq_one_of_isAssociatedPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:53.647181+00:00
-- url     : https://prove2.me/submissions/7cb9be52-e89a-47c0-b657-bd7208451724

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_KrullDomain
import Theorems.Thm_GroundTheory_Arith_Toric_smul_mk_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {b : A} (hb : b ≠ 0) {P : Ideal A}
    (hP : IsAssociatedPrime P (A ⧸ Ideal.span {b})) : P.height = 1 := by
  classical
  obtain ⟨hPp, yb, hPy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yb
  have hmem : ∀ r, r ∈ P ↔ b ∣ r * y := by
    intro r
    rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_mk_eq_zero_iff]
  have hbP : b ∈ P := (hmem b).2 (dvd_mul_right b y)
  have hP0 : P ≠ ⊥ := fun h => hb (by rw [h] at hbP; exact (Submodule.mem_bot _).1 hbP)
  by_cases hcase : ∀ r s : A, r ∈ P → r * y = b * s → s ∈ P
  · exfalso
    let K := FractionRing A
    have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) P
    have hNfg : N.FG := (IsNoetherian.noetherian P).map _
    have hN0 : N ≠ ⊥ := by
      intro h
      have : algebraMap A K b ∈ N := Submodule.mem_map.2 ⟨b, hbP, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hb (hinj (by rw [this, map_zero]))
    have hbK : algebraMap A K b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hint : IsIntegral A (algebraMap A K y / algebraMap A K b) := by
      refine isIntegral_of_smul_mem_submodule N hN0 hNfg _ ?_
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨s, hs⟩ := (hmem r).1 hr
      refine Submodule.mem_map.2 ⟨s, hcase r s hr hs, ?_⟩
      change algebraMap A K s = (algebraMap A K y / algebraMap A K b) * algebraMap A K r
      rw [div_mul_eq_mul_div, eq_div_iff hbK, ← map_mul, ← map_mul, mul_comm y r, hs, mul_comm]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hyz : y = b * z := by
      apply hinj
      rw [map_mul, hz, mul_div_cancel₀ _ hbK]
    apply hPp.ne_top
    rw [Ideal.eq_top_iff_one, hmem, one_mul, hyz]
    exact dvd_mul_right b z
  · push Not at hcase
    obtain ⟨r₀, s₀, hr₀, hrs, hs₀⟩ := hcase
    have hmin : P ∈ (Ideal.span {r₀}).minimalPrimes := by
      refine ⟨⟨hPp, (Ideal.span_singleton_le_iff_mem _).2 hr₀⟩, fun Q hQ hQP => ?_⟩
      obtain ⟨hQp, hQr⟩ := hQ
      intro r hr
      obtain ⟨s, hs⟩ := (hmem r).1 hr
      have key : r * s₀ = r₀ * s := by
        apply mul_left_cancel₀ hb
        calc b * (r * s₀) = r * (b * s₀) := by ring
          _ = r * (r₀ * y) := by rw [hrs]
          _ = r₀ * (r * y) := by ring
          _ = b * (r₀ * s) := by rw [hs]; ring
      have hin : r * s₀ ∈ Q := by
        rw [key]
        exact Q.mul_mem_right s ((Ideal.span_singleton_le_iff_mem _).1 hQr)
      exact (hQp.mem_or_mem hin).resolve_right fun h => hs₀ (hQP h)
    have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {r₀}) P hmin
    have hne : P.height ≠ 0 := fun h => hP0 (Ideal.height_eq_zero_iff_eq_bot.1 h)
    exact le_antisymm hle (Order.one_le_iff_ne_zero.2 hne)
end GroundTheory.Arith.Toric
