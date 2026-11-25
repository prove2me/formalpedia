-- Prove2me | solution 1 for GlobalTheory.mem_span_prime_of_not_isUnit_of_pow_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:19.373035+00:00
-- url     : https://prove2.me/submissions/44570283-8004-43ef-8123-f6cfe1e31e08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HomValueCongruentIntModPrime

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
theorem _root_.solution {O : Type} [CommRing O] [IsLocalRing O] (g : ℕ)
    (hg : g.Prime) (y : O) (hy : y ^ g - y ∈ Ideal.span {(g : O)}) (hn : ¬ IsUnit y) :
    y ∈ Ideal.span {(g : O)} := by
  have hm : y ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal y).mpr hn
  have hpos : 1 ≤ g - 1 := by have := hg.two_le; omega
  have hz : y ^ (g - 1) ∈ IsLocalRing.maximalIdeal O := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hpos
    rw [hk, pow_add, pow_one]
    exact Ideal.mul_mem_right _ _ hm
  obtain ⟨u, hu⟩ := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    ((IsLocalRing.mem_maximalIdeal _).mp hz)
  have e : y ^ g = y * y ^ (g - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hg.one_lt.le]
  have hy' : y = -(y ^ g - y) * ↑u⁻¹ := by
    calc y = y * (↑u * ↑u⁻¹) := by simp
      _ = -(y ^ g - y) * ↑u⁻¹ := by rw [hu, e]; ring
  rw [hy']
  exact Ideal.mul_mem_right _ _ (neg_mem hy)
end GlobalTheory
