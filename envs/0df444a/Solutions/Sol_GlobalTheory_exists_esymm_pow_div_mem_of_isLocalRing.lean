-- Prove2me | solution 1 for GlobalTheory.exists_esymm_pow_div_mem_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:29.431138+00:00
-- url     : https://prove2.me/submissions/243efb03-085d-46b0-b62e-245f5a4d5f4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEsymmPowDivMemOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Field K] (O : Subring K) [IsLocalRing O] (A : Type) [Fintype A] (x : A → K) (D k : ℕ) (c : K), 1 ≤ D → 1 ≤ k → k ∣ D → c ≠ 0 → (Finset.univ.val.map x).esymm k ^ (D / k) = c → (∀ a, x a ^ D / c ∈ O) → ∃ a, x a ≠ 0 ∧ c / x a ^ D ∈ O := by
  intro K _ O _ A _ x D k c hD hk hkD hc hce hO
  obtain ⟨V, hle, hloc⟩ := (LocalSubring.mk O).exists_le_valuationSubring
  have hkD' : 0 < D / k := Nat.div_pos (Nat.le_of_dvd (by omega) hkD) (by omega)
  have hes : (Finset.univ.val.map x).esymm k = ∑ t ∈ (Finset.univ : Finset A).powersetCard k, ∏ b ∈ t, x b :=
    Finset.esymm_map_val x _ k
  rcases isEmpty_or_nonempty A with hA | hA
  · exfalso
    apply hc
    rw [← hce, hes, Finset.powersetCard_eq_empty.2 (by simp; omega), Finset.sum_empty, zero_pow hkD'.ne']
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image (Finset.univ : Finset A) (fun b => V.valuation (x b))
    Finset.univ_nonempty
  have hvc : V.valuation c ≠ 0 := by simpa using hc
  have h1 : V.valuation (x a) ^ D ≤ V.valuation c := by
    have := (V.valuation_le_one_iff _).2 (hle (hO a))
    rw [map_div₀, map_pow] at this
    exact (div_le_one₀ (zero_lt_iff.2 hvc)).1 this
  have h2 : V.valuation c ≤ V.valuation (x a) ^ D := by
    rw [← hce, map_pow, hes]
    have hb : V.valuation (∑ t ∈ (Finset.univ : Finset A).powersetCard k, ∏ b ∈ t, x b) ≤ V.valuation (x a) ^ k := by
      refine Valuation.map_sum_le _ (fun t ht => ?_)
      rw [map_prod]
      have hcard := (Finset.mem_powersetCard.1 ht).2
      rw [← hcard]
      exact Finset.prod_le_pow_card _ _ _ (fun b _ => ha b (Finset.mem_univ b))
    calc _ ≤ (V.valuation (x a) ^ k) ^ (D / k) := pow_le_pow_left₀ zero_le' hb _
      _ = V.valuation (x a) ^ D := by rw [← pow_mul, Nat.mul_div_cancel' hkD]
  have heq : V.valuation (x a) ^ D = V.valuation c := le_antisymm h1 h2
  have hxa : x a ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_pow (by omega)] at heq
    exact hvc heq.symm
  refine ⟨a, hxa, ?_⟩
  let y : O := ⟨x a ^ D / c, hO a⟩
  have hyV : IsUnit (Subring.inclusion hle y) := by
    refine (V.valuation_eq_one_iff ⟨x a ^ D / c, hle (hO a)⟩).2 ?_
    show V.valuation (x a ^ D / c) = 1
    rw [map_div₀, map_pow, heq, div_self hvc]
  have hy : IsUnit y := hloc.map_nonunit _ hyV
  obtain ⟨u, hu⟩ := hy
  have : ((u⁻¹ : Oˣ) : O) = c / x a ^ D := by
    have h3 : ((u : O) : K) * (((u⁻¹ : Oˣ) : O) : K) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    rw [hu] at h3
    have h4 : (x a ^ D / c) * (((u⁻¹ : Oˣ) : O) : K) = 1 := h3
    show (((u⁻¹ : Oˣ) : O) : K) = c / x a ^ D
    rw [eq_inv_of_mul_eq_one_right h4, inv_div]
  rw [← this]
  exact ((u⁻¹ : Oˣ) : O).2
end GlobalTheory
