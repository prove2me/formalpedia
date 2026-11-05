-- Prove2me | solution 1 for LL_Decomp126b.pocklington_divisors
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:21.366073+00:00
-- url     : https://prove2.me/submissions/e4194a40-edbf-4d3b-9e88-7c2bd434dd99

import Mathlib

theorem solution {N R F : ℕ} (hN2 : 2 ≤ N) (hF2 : 2 ≤ F)
    (hN : N = R * F + 1) {a : ℤ} (ha : Int.ModEq (N : ℤ) (a ^ (N - 1)) 1)
    (hgcd : ∀ p : ℕ, p.Prime → p ∣ F → Int.gcd (a ^ ((N - 1) / p) - 1) N = 1) :
    ∀ d : ℕ, d ∣ N → 1 < d → ∃ k : ℕ, 0 < k ∧ d = k * F + 1 := by
  have hm : N - 1 = R * F := by omega
  have hprime : ∀ q : ℕ, q.Prime → q ∣ N → F ∣ q - 1 := by
    intro q hq hqN
    have := Fact.mk hq
    have hxN : ((a : ZMod q)) ^ (N - 1) = 1 := by
      have h1 : Int.ModEq (q : ℤ) (a ^ (N - 1)) 1 :=
        Int.ModEq.of_dvd (by exact_mod_cast hqN) ha
      have := (ZMod.intCast_eq_intCast_iff _ _ q).mpr h1
      push_cast at this
      exact this
    have hx0 : (a : ZMod q) ≠ 0 := by
      intro h
      rw [h, zero_pow (by omega)] at hxN
      exact zero_ne_one hxN
    have hqmin : orderOf (a : ZMod q) ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one hx0
    have hord : orderOf (a : ZMod q) ∣ N - 1 := orderOf_dvd_of_pow_eq_one hxN
    have hFo : F ∣ orderOf (a : ZMod q) := by
      rw [Nat.dvd_iff_prime_pow_dvd_dvd]
      intro p k hp hpk
      by_contra hnot
      have hk : k ≠ 0 := by
        rintro rfl
        simp at hnot
      have hpF : p ∣ F := (dvd_pow_self p hk).trans hpk
      have hpm : p ∣ N - 1 := by rw [hm]; exact hpF.trans (dvd_mul_left F R)
      have hkm : p ^ k ∣ N - 1 := by rw [hm]; exact hpk.trans (dvd_mul_left F R)
      have hdiv : orderOf (a : ZMod q) ∣ (N - 1) / p := by
        rw [Nat.dvd_iff_prime_pow_dvd_dvd]
        intro r j hr hrj
        have hrm : r ^ j ∣ N - 1 := hrj.trans hord
        by_cases hrp : r = p
        · subst hrp
          have hjk : j < k := by
            by_contra hh
            push Not at hh
            exact hnot ((pow_dvd_pow r hh).trans hrj)
          apply Nat.dvd_div_of_mul_dvd
          rw [← pow_succ']
          exact (pow_dvd_pow r (Nat.succ_le_of_lt hjk)).trans hkm
        · have hcop : Nat.Coprime (r ^ j) p :=
            Nat.Coprime.pow_left j ((Nat.coprime_primes hr hp).mpr hrp)
          apply hcop.dvd_of_dvd_mul_left
          rw [Nat.mul_div_cancel' hpm]
          exact hrm
      have hxp : (a : ZMod q) ^ ((N - 1) / p) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdiv
      have h3 : (q : ℤ) ∣ a ^ ((N - 1) / p) - 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [hxp, sub_self]
      have h4 : (q : ℤ) ∣ (Int.gcd (a ^ ((N - 1) / p) - 1) N : ℤ) :=
        Int.dvd_coe_gcd h3 (by exact_mod_cast hqN)
      rw [hgcd p hp hpF] at h4
      have h5 : q ∣ 1 := by exact_mod_cast h4
      exact hq.one_lt.ne' (Nat.dvd_one.mp h5)
    exact hFo.trans hqmin
  have hmain : ∀ d : ℕ, d ∣ N → ∃ k : ℕ, d = k * F + 1 := by
    intro d
    induction d using induction_on_primes with
    | zero =>
      intro h
      exact absurd (Nat.eq_zero_of_zero_dvd h) (by omega)
    | one => intro _; exact ⟨0, by simp⟩
    | prime_mul p b hp ih =>
      intro h
      obtain ⟨k1, hk1⟩ := ih ((dvd_mul_left b p).trans h)
      obtain ⟨c, hc⟩ := hprime p hp ((dvd_mul_right p b).trans h)
      have hp1 : p = c * F + 1 := by
        have := hp.two_le
        rw [mul_comm] at hc
        omega
      refine ⟨c * k1 * F + c + k1, ?_⟩
      rw [hp1, hk1]; ring
  intro d hd hd1
  obtain ⟨k, hk⟩ := hmain d hd
  refine ⟨k, ?_, hk⟩
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0; simp at hk; omega
  · exact h0
