-- Prove2me | solution 1 for LongGapsBetweenPrimes.short_translates_with_sieveDelta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:20:59.061596+00:00
-- url     : https://prove2.me/submissions/ca6587ad-e0e1-4888-b921-630671816053

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_mem_auxiliaryPrimes
import Theorems.Thm_LongGapsBetweenPrimes_prime_dvd_auxiliaryProduct
import Theorems.Thm_LongGapsBetweenPrimes_sieveZ_lower
import Theorems.Thm_LongGapsBetweenPrimes_eventually_simultaneous_roots
import Theorems.Thm_LongGapsBetweenPrimes_eventually_sieveY_lt_primorial
import Theorems.Thm_LongGapsBetweenPrimes_exists_linear_roots

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x < H → (H : ℝ) ≤ x * (Real.log x) ^ 2 →
    ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 H → (S.card : ℝ) ≤ sieveDelta * x →
    ∀ b : ℕ, b < primorial ⌊x⌋₊ →
    ∃ t : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ Real.exp x ∧
      ∀ s ∈ S, ¬Nat.Prime (b + primorial ⌊x⌋₊ * t + s) := by
  classical
  filter_upwards [eventually_simultaneous_roots, eventually_sieveY_lt_primorial,
    Filter.eventually_ge_atTop (2 : ℝ)] with x hroots hY hx
  intro H hxH hH S hS hcard b hb
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hHZ : H < sieveZ x := by
    have hlog : Real.log x ≤ x := by
      linarith [Real.log_le_sub_one_of_pos hx0]
    have hH' : (H : ℝ) ≤ x ^ 4 := calc
      (H : ℝ) ≤ x * (Real.log x) ^ 2 := hH
      _ ≤ x * x ^ 2 := by gcongr; exact Real.log_nonneg hx1
      _ = x ^ 3 := by ring
      _ ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by decide)
    exact_mod_cast hH'.trans_lt (by linarith [sieveZ_lower hx] : x ^ 4 < (sieveZ x : ℝ))
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, le_rfl, by simpa using Real.one_le_exp hx0.le, by simp⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne.card_pos.ne'
  let e : Fin (k + 1) ≃ S :=
    (Fintype.equivFinOfCardEq (by simpa using hk : Fintype.card S = k + 1)).symm
  let s : Fin (k + 1) → ℕ := fun i => (e i).val
  have hp_bounds (p : PrimeIndex (sieveP x)) :
      p.val.Prime ∧ H < p.val ∧ p.val < primorial ⌊x⌋₊ := by
    obtain ⟨hp, hdvd, _⟩ := Nat.mem_primeFactors.mp p.property
    obtain ⟨_, hpZ, hpY⟩ := mem_auxiliaryPrimes.mp (prime_dvd_auxiliaryProduct hp hdvd)
    exact ⟨hp, hHZ.trans hpZ, hpY.trans_lt hY⟩
  have hlinear (p : PrimeIndex (sieveP x)) :
      ∃ root : Fin (k + 1) → Fin p.val, Function.Injective root ∧
        ∀ n i, n % p.val = (root i).val →
          p.val ∣ b + primorial ⌊x⌋₊ * (n + 1) + s i := by
    obtain ⟨hp, hHp, _⟩ := hp_bounds p
    have hpx : ⌊x⌋₊ < p.val :=
      (Nat.floor_lt hx0.le).mpr (hxH.trans (by exact_mod_cast hHp))
    have hcop : (primorial ⌊x⌋₊).Coprime p.val :=
      (hp.coprime_iff_not_dvd.mpr (hp.dvd_primorial_iff.not.mpr hpx.not_ge)).symm
    exact exists_linear_roots hp hcop s (Subtype.val_injective.comp e.injective)
      (fun i => (Finset.mem_Icc.mp (hS (e i).property)).2.trans_lt hHp)
  choose root hinj hdiv using hlinear
  obtain ⟨n, hn, hhit⟩ := hroots k (by simpa [hk] using hcard) root hinj
  refine ⟨n + 1, by omega, ?_, ?_⟩
  · exact (by exact_mod_cast hn : ((n + 1 : ℕ) : ℝ) ≤ sieveT x).trans
      (Nat.floor_le (Real.exp_pos x).le)
  · intro a ha hprime
    obtain ⟨i, hi⟩ := e.surjective ⟨a, ha⟩
    obtain ⟨p, hp⟩ := hhit i
    have hdvd := hdiv p n i (congrArg Fin.val hp)
    have hsi : s i = a := congrArg Subtype.val hi
    rw [hsi] at hdvd
    obtain ⟨hpprime, _, hpQ⟩ := hp_bounds p
    have hQ : primorial ⌊x⌋₊ ≤ primorial ⌊x⌋₊ * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hlt : p.val < b + primorial ⌊x⌋₊ * (n + 1) + a := by omega
    exact (hprime.eq_one_or_self_of_dvd _ hdvd).elim hpprime.ne_one (ne_of_lt hlt)
end LongGapsBetweenPrimes
