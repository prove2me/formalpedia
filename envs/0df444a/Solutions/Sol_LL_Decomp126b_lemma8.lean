-- Prove2me | solution 1 for LL_Decomp126b.lemma8
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:22.629649+00:00
-- url     : https://prove2.me/submissions/5a851881-18cf-418d-834d-2c0de094b53d

import Mathlib
import Definitions.Def_LL_Decomp126b_lemma8_stmt

namespace GbBAux

theorem pocklington_divisors {N R F : ℕ} (hN2 : 2 ≤ N) (hF2 : 2 ≤ F)
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

end GbBAux

theorem solution : LL_Decomp126b.lemma8_stmt := by
  unfold LL_Decomp126b.lemma8_stmt
  have hSPgen : ∀ x y : ℕ, 1 ≤ x → 1 ≤ y → x + y ≤ x * y + 1 := by
    intro x y hx hy
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hx
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hy
    nlinarith [Nat.zero_le (a * b)]
  have hkey : ∀ a b : ℤ, -2 < 2 * a - 2 * b → 2 * a - 2 * b < 2 → a = b := by
    intro a b h1 h2
    omega
  intro N R F s r hN2 hF2 hFeven hcop hNodd hN hR hr hNlt ⟨a, ha, hgcd⟩
  have hF0 : 0 < F := by omega
  -- a nontrivial factorisation of N gives s ≠ 0 and a square
  have hfact : s ≠ 0 → IsSquare ((r : ℤ) ^ 2 - 8 * s) → ¬ N.Prime := by
    intro hs ⟨t, ht⟩
    have hu : ((t.natAbs : ℕ) : ℤ) * (t.natAbs : ℕ) = t * t := Int.natAbs_mul_self' t
    obtain ⟨u, hu0⟩ : ∃ u : ℕ, u = t.natAbs := ⟨_, rfl⟩
    rw [← hu0] at hu
    have hru : r * r = u * u + 8 * s := by
      have : (r : ℤ) * r = u * u + 8 * s := by nlinarith [ht, hu]
      exact_mod_cast this
    have hs1 : 1 ≤ s := Nat.pos_of_ne_zero hs
    have hur : u < r := by
      by_contra h
      push Not at h
      have := Nat.mul_le_mul h h
      omega
    have hpar : (r + u) % 2 = 0 := by
      have h1 := Nat.mul_mod r r 2
      have h2 := Nat.mul_mod u u 2
      rcases Nat.mod_two_eq_zero_or_one r with hr0 | hr0 <;>
        rcases Nat.mod_two_eq_zero_or_one u with hu0 | hu0 <;>
        rw [hr0] at h1 <;> rw [hu0] at h2 <;> omega
    obtain ⟨w, hw⟩ : ∃ w, r + u = w + w := ⟨(r + u) / 2, by omega⟩
    obtain ⟨c2, hc2⟩ : ∃ c2, r = w + c2 := ⟨r - w, by omega⟩
    have hu2 : (u : ℤ) = w - c2 := by omega
    have hwc : w * c2 = 2 * s := by
      have hru' : (r : ℤ) * r = u * u + 8 * s := by exact_mod_cast hru
      have hr2 : (r : ℤ) = w + c2 := by exact_mod_cast hc2
      rw [hu2, hr2] at hru'
      have : (w : ℤ) * c2 = 2 * s := by nlinarith [hru']
      exact_mod_cast this
    have hw1 : 1 ≤ w := by omega
    have hc21 : 1 ≤ c2 := by omega
    have hNe : N = (w * F + 1) * (c2 * F + 1) := by
      rw [hN, hR, hc2]
      calc (2 * F * s + (w + c2)) * F + 1 = (2 * s) * F ^ 2 + (w + c2) * F + 1 := by ring
        _ = (w * c2) * F ^ 2 + (w + c2) * F + 1 := by rw [hwc]
        _ = _ := by ring
    rw [hNe]
    apply Nat.not_prime_mul
    · have := Nat.mul_pos hw1 hF0
      omega
    · have := Nat.mul_pos hc21 hF0
      omega
  have hcomp : ¬ N.Prime → (s ≠ 0 ∧ IsSquare ((r : ℤ) ^ 2 - 8 * s)) := by
    intro hnp
    obtain ⟨d, hdN, hd2, hdlt⟩ := Nat.exists_dvd_of_not_prime2 hN2 hnp
    obtain ⟨e, he⟩ := hdN
    have he1 : 1 < e := by
      rcases Nat.lt_or_ge 1 e with h | h
      · exact h
      · interval_cases e <;> omega
    have hpd := GbBAux.pocklington_divisors hN2 hF2 hN ha hgcd
    obtain ⟨c1, hc1, hd⟩ := hpd d ⟨e, he⟩ (by omega)
    obtain ⟨c2, hc2, he'⟩ := hpd e ⟨d, by rw [he, mul_comm]⟩ he1
    have h1 : R * F + 1 = (c1 * F + 1) * (c2 * F + 1) := by
      rw [← hN, he, hd, he']
    have hRPS : R = c1 * c2 * F + (c1 + c2) := by
      have h2 : R * F = (c1 * c2 * F + (c1 + c2)) * F := by nlinarith [h1]
      exact Nat.eq_of_mul_eq_mul_right hF0 h2
    obtain ⟨f, hf⟩ := hFeven
    have hRodd : R % 2 = 1 := by
      by_contra hR2
      have h2R : 2 ∣ R := by omega
      have h2F : 2 ∣ F := ⟨f, by omega⟩
      have := Nat.dvd_gcd h2R h2F
      rw [hcop.gcd_eq_one] at this
      omega
    have hPF : c1 * c2 * F = 2 * (c1 * c2 * f) := by rw [hf]; ring
    have hS : (c1 + c2) % 2 = 1 := by omega
    have hP2 : (c1 * c2) % 2 = 0 := by
      have h := Nat.mul_mod c1 c2 2
      rcases Nat.mod_two_eq_zero_or_one c1 with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one c2 with h2 | h2 <;>
        rw [h1, h2] at h <;> omega
    have hPlt : c1 * c2 < 2 * F := by
      have h3 : c1 * c2 * F ^ 2 < 2 * F * F ^ 2 := by
        have e : N = c1 * c2 * F ^ 2 + (c1 + c2) * F + 1 := by rw [hN, hRPS]; ring
        have e' : 2 * F * F ^ 2 = 2 * F ^ 3 := by ring
        omega
      exact Nat.lt_of_mul_lt_mul_right h3
    have hSP : c1 + c2 ≤ c1 * c2 + 1 := hSPgen c1 c2 hc1 hc2
    have hSlt : c1 + c2 < 2 * F := by omega
    obtain ⟨w, hw⟩ : ∃ w, c1 * c2 = 2 * w := ⟨c1 * c2 / 2, by omega⟩
    have e1 : (R : ℤ) = c1 * c2 * F + (c1 + c2) := by exact_mod_cast hRPS
    have e2 : (R : ℤ) = 2 * F * s + r := by exact_mod_cast hR
    have hj : (2 * (w : ℤ) - 2 * s) * F = r - (c1 + c2) := by
      have hw' : (c1 : ℤ) * c2 = 2 * w := by exact_mod_cast hw
      rw [← hw']
      linear_combination e2 - e1
    have hFz : (0 : ℤ) < F := by exact_mod_cast hF0
    have hrz : (r : ℤ) < 2 * F := by exact_mod_cast hr
    have hSz : (c1 : ℤ) + c2 < 2 * F := by exact_mod_cast hSlt
    have hj1 : 2 * (w : ℤ) - 2 * s < 2 := by
      by_contra h
      push Not at h
      have := mul_le_mul_of_nonneg_right h hFz.le
      have : (0 : ℤ) ≤ c1 + c2 := by positivity
      linarith
    have hj2 : -2 < 2 * (w : ℤ) - 2 * s := by
      by_contra h
      push Not at h
      have := mul_le_mul_of_nonneg_right h hFz.le
      have : (0 : ℤ) ≤ r := by positivity
      linarith
    have hws : (w : ℤ) = s := hkey w s hj2 hj1
    have hrS : (r : ℤ) = c1 + c2 := by
      rw [hws] at hj
      have : (2 * (s : ℤ) - 2 * s) * F = 0 := by ring
      linarith
    refine ⟨?_, c1 - c2, ?_⟩
    · intro hs0
      subst hs0
      have : c1 * c2 = 0 := by omega
      have := Nat.mul_pos hc1 hc2
      omega
    · have hw' : (c1 : ℤ) * c2 = 2 * w := by exact_mod_cast hw
      rw [hrS]
      linear_combination 4 * hw' + 8 * hws
  constructor
  · intro hp
    by_contra hcon
    push Not at hcon
    exact hfact hcon.1 hcon.2 hp
  · intro h
    by_contra hnp
    obtain ⟨h1, h2⟩ := hcomp hnp
    rcases h with h | h
    · exact h1 h
    · exact h h2
