-- Prove2me | solution 1 for GlobalTheory.wittVector_eq_teichmuller_of_frobenius_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:52:38.17082+00:00
-- url     : https://prove2.me/submissions/833ef63f-49c8-4de7-9ddc-6008a951bddf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorEqTeichmullerOfFrobeniusEqPowSelf
import Theorems.Thm_GlobalTheory_wittVector_iterate_frobenius_of_eq_pow
import Theorems.Thm_GlobalTheory_wittVector_coeff_iterate_frobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory
open WittVector
namespace GlobalTheory
theorem _root_.solution :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [CharP O l] [PerfectRing O l]
      (y : WittVector l O), WittVector.frobenius y = y ^ l →
      y = WittVector.teichmuller l (y.coeff 0) := by
  intro l _ O _ _ _ y h

  have hdiv : (l : WittVector l O) ∣ y - WittVector.teichmuller l (y.coeff 0) := by
    have h0 : ∀ i < 1, (y - WittVector.teichmuller l (y.coeff 0)).coeff i = 0 := by
      intro i hi
      obtain rfl : i = 0 := by omega
      have hc := map_sub (WittVector.constantCoeff (p := l) (R := O)) y
        (WittVector.teichmuller l (y.coeff 0))
      simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self] at hc
      exact hc
    obtain ⟨w, hw⟩ := (WittVector.frobenius_bijective l O).2
      ((y - WittVector.teichmuller l (y.coeff 0)).shift 1)
    refine ⟨w, ?_⟩
    rw [WittVector.eq_iterate_verschiebung h0, Function.iterate_one, ← hw,
      WittVector.verschiebung_frobenius, mul_comm]
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [WittVector.teichmuller_coeff_pos l _ n hn]

  obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub hdiv n
  have hy : y ^ l ^ n = WittVector.teichmuller l (y.coeff 0 ^ l ^ n) +
      c * (l : WittVector l O) ^ (n + 1) := by
    rw [map_pow, mul_comm c]
    exact sub_eq_iff_eq_add'.mp hc
  have hcoeff : (y ^ l ^ n).coeff n = 0 := by
    rw [hy, WittVector.coeff_add_of_disjoint]
    · rw [WittVector.teichmuller_coeff_pos l _ n hn,
        WittVector.mul_pow_charP_coeff_zero _ (by omega : n < n + 1), add_zero]
    · intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact Or.inr (WittVector.mul_pow_charP_coeff_zero _ (by omega))
      · exact Or.inl (WittVector.teichmuller_coeff_pos l _ m hm)

  rw [← wittVector_iterate_frobenius_of_eq_pow y h n, wittVector_coeff_iterate_frobenius] at hcoeff
  apply (bijective_iterateFrobenius O l n).1
  show y.coeff n ^ l ^ n = (0 : O) ^ l ^ n
  rw [hcoeff, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
end GlobalTheory
