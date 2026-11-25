-- Prove2me | solution 1 for GlobalTheory.MinkowskiOrder.sum_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:07:05.081827+00:00
-- url     : https://prove2.me/submissions/f662a110-49e5-4207-891f-d703d025d2e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsInvariantNatLengthLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardFiniteSubgroupGLIntDvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.MinkowskiOrder
namespace GlobalTheory.MinkowskiOrder
theorem _root_.solution (p l : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hl : l.Prime) (hpl : p < l)
    (h : ∀ i, p ^ 2 ∣ l ^ i - 1 → p * (p - 1) ∣ i) (n : ℕ) :
    ∑ i ∈ Finset.range n, padicValNat p (l ^ (i + 1) - 1)
      ≤ n / (p - 1) + padicValNat p (n / (p - 1)).factorial := by
  haveI := Fact.mk hp
  have hp2 := hp.two_le
  have hodd : Odd p := hp.odd_of_ne_two h2
  have hnd : ∀ k, ¬ p ∣ l ^ k := fun k hk => by
    have := (Nat.prime_dvd_prime_iff_eq hp hl).mp (hp.dvd_of_dvd_pow hk)
    omega
  have hlte : ∀ k m, k ≠ 0 → m ≠ 0 → p ∣ l ^ k - 1 →
      padicValNat p (l ^ (k * m) - 1) = padicValNat p (l ^ k - 1) + padicValNat p m := by
    intro k m hk hm hd
    have := padicValNat.pow_sub_pow (p := p) (x := l ^ k) (y := 1) hodd
      (Nat.one_lt_pow hk hl.one_lt) hd (hnd k) hm
    rwa [one_pow, ← pow_mul] at this
  have hne : ∀ k, k ≠ 0 → l ^ k - 1 ≠ 0 := fun k hk =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hk hl.one_lt)
  have hferm : p ∣ l ^ (p - 1) - 1 := by
    have hc : l.Coprime p := (Nat.coprime_primes hl hp).mpr (by omega)
    have := Nat.ModEq.pow_totient hc
    rw [Nat.totient_prime hp] at this
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hl.pos)).mp this.symm
  have hone : padicValNat p (l ^ (p - 1) - 1) ≤ 1 := by
    by_contra hc
    have h0 := h (p - 1) ((padicValNat_dvd_iff_le (hne (p - 1) (by omega))).mpr (by omega))
    have := Nat.le_of_dvd (by omega) h0
    have h3 : 2 * (p - 1) ≤ p * (p - 1) := Nat.mul_le_mul_right _ hp2
    omega
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.succ_div]
    split_ifs with hd
    · have e : n + 1 = (p - 1) * (n / (p - 1) + 1) := by
        have := Nat.succ_div_of_dvd hd
        rw [← this, Nat.mul_div_cancel' hd]
      rw [Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _)]
      have := hlte (p - 1) (n / (p - 1) + 1) (by omega) (Nat.succ_ne_zero _) hferm
      rw [← e] at this
      simp only [Nat.succ_eq_add_one]
      omega
    · have : padicValNat p (l ^ (n + 1) - 1) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        intro hd'
        have h1 := hlte (n + 1) p (by omega) (by omega) hd'
        have h3 := one_le_padicValNat_of_dvd (hne (n + 1) (by omega)) hd'
        rw [padicValNat_self] at h1
        have h4 := h _ ((padicValNat_dvd_iff_le (hne ((n + 1) * p)
          (Nat.mul_ne_zero (by omega) (by omega)))).mpr (by omega : 2 ≤ _))
        rw [mul_comm (n + 1)] at h4
        exact hd (Nat.dvd_of_mul_dvd_mul_left hp.pos h4)
      simp only [add_zero]
      omega
end GlobalTheory.MinkowskiOrder
