-- Prove2me | solution 1 for MvPowerSeries.exists_wittVector_forall_coeff_ghostComponent_eq_logCovector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/cb14642b-4e7a-5716-87e7-1df9c0d30d81

import Mathlib
import Theorems.Thm_WittVector_exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem
import Theorems.Thm_MvPowerSeries_expand_sub_pow_mem_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_logCovector

set_option autoImplicit false

namespace S17LCov

open MvPowerSeries

variable {𝓞 : Type*} [CommRing 𝓞] {p : ℕ} [hp : Fact p.Prime] {d : ℕ}

omit hp in
theorem mem_span_pow_of_forall_coeff_mem {σ : Type*} {g : MvPowerSeries σ 𝓞} (e : ℕ)
    (h : ∀ m, coeff m g ∈ Ideal.span {(p : 𝓞) ^ e}) : g ∈ Ideal.span {(p : MvPowerSeries σ 𝓞) ^ e} := by
  choose b hb using fun m => Ideal.mem_span_singleton'.1 (h m)
  refine Ideal.mem_span_singleton'.2 ⟨(fun m => b m : MvPowerSeries σ 𝓞), ?_⟩
  ext m
  rw [← map_natCast (C (σ := σ) (R := 𝓞)) p, ← map_pow, coeff_mul_C, ← hb m]
  rfl

omit hp in

theorem mem_span_pow_of_pow_mul_mem (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {a : 𝓞} {K e : ℕ} (hKe : K ≤ e)
    (h : (p : 𝓞) ^ K * a ∈ Ideal.span {(p : 𝓞) ^ e}) : a ∈ Ideal.span {(p : 𝓞) ^ (e - K)} := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
  refine Ideal.mem_span_singleton'.2 ⟨b, ?_⟩
  have h0 : (p : 𝓞) ^ K * (b * (p : 𝓞) ^ (e - K) - a) = 0 := by
    rw [mul_sub, sub_eq_zero, ← hb, mul_comm ((p : 𝓞) ^ K), mul_assoc, ← pow_add, Nat.sub_add_cancel hKe]
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 (pow_mem hpR K)).1 _ h0)

theorem mem_span_pow_of_natCast_mul_mem {u : ℕ} (hu : ¬ p ∣ u) {a : 𝓞} {e : ℕ}
    (h : (u : 𝓞) * a ∈ Ideal.span {(p : 𝓞) ^ e}) : a ∈ Ideal.span {(p : 𝓞) ^ e} := by
  have hcop : IsCoprime (u : ℤ) ((p : ℤ) ^ e) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu).symm)
  obtain ⟨x, y, hxy⟩ := hcop
  have h1 : ((x : 𝓞) * (u : 𝓞) + (y : 𝓞) * (p : 𝓞) ^ e) = 1 := by
    have := congrArg (Int.castRingHom 𝓞) hxy
    simpa using this
  have : a = (x : 𝓞) * ((u : 𝓞) * a) + (p : 𝓞) ^ e * ((y : 𝓞) * a) := by
    calc a = ((x : 𝓞) * (u : 𝓞) + (y : 𝓞) * (p : 𝓞) ^ e) * a := by rw [h1, one_mul]
      _ = _ := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

omit hp in

theorem natCast_mul_coeff_mem (φi : MvPowerSeries (Fin d) 𝓞)
    (hint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * coeff (m + Finsupp.single j 1) φi ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (M' : Fin d →₀ ℕ) (i : Fin d) (hi : 1 ≤ M' i) :
    ((M' i : ℕ) : 𝓞) * coeff M' φi ∈ Ideal.span {(p : 𝓞) ^ (M'.degree - 1)} := by
  have hle : Finsupp.single i 1 ≤ M' := Finsupp.single_le_iff.2 hi
  set m := M' - Finsupp.single i 1 with hm
  have hM : m + Finsupp.single i 1 = M' := tsub_add_cancel_of_le hle
  have h1 : m i + 1 = M' i := by
    conv_rhs => rw [← hM]
    simp
  have h2 : m.degree = M'.degree - 1 := by
    conv_rhs => rw [← hM]
    rw [map_add, Finsupp.degree_single]
    simp
  have := hint i m
  rwa [h1, hM, h2] at this

omit hp in
theorem succ_le_prime_pow (hp1 : 1 < p) (K : ℕ) : K + 1 ≤ p ^ K := Nat.lt_pow_self hp1

theorem c_smul_mem (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (φi : MvPowerSeries (Fin d) 𝓞)
    (hint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * coeff (m + Finsupp.single j 1) φi ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (N : ℕ) (c : (Fin d →₀ ℕ) → 𝓞)
    (hc : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ N → c m = (p : 𝓞) ^ (N - m.degree) * coeff m φi) ∧
      (N < m.degree → c m * (p : 𝓞) ^ (m.degree - N) = coeff m φi ∨
        (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ coeff m φi)))
    (K : ℕ) (hK : K + 1 ≤ N) (M : Fin d →₀ ℕ) (i : Fin d) (hi : ¬ p ∣ M i) :
    c (p ^ K • M) ∈ Ideal.span {(p : 𝓞) ^ (N - 1 - K)} := by
  set M' := p ^ K • M with hM'
  have hMi : 1 ≤ M i := Nat.one_le_iff_ne_zero.2 (fun h => hi (h ▸ dvd_zero p))
  have hM'i : M' i = p ^ K * M i := by simp [hM']
  have hdeg : M'.degree = p ^ K * M.degree := by rw [hM', map_nsmul, smul_eq_mul]
  have hdeg1 : K + 1 ≤ M'.degree := by
    rw [hdeg]
    calc K + 1 ≤ p ^ K := succ_le_prime_pow hp.out.one_lt K
      _ = p ^ K * 1 := (mul_one _).symm
      _ ≤ p ^ K * M.degree := Nat.mul_le_mul_left _ (hMi.trans (Finsupp.le_degree i M))

  have hA := natCast_mul_coeff_mem φi hint M' i (by rw [hM'i]; exact Nat.mul_pos (pow_pos hp.out.pos K) hMi)
  rw [hM'i, Nat.cast_mul, Nat.cast_pow, mul_comm ((p : 𝓞) ^ K) (M i : 𝓞), mul_assoc] at hA
  have hB := mem_span_pow_of_pow_mul_mem hpR (by omega) (mem_span_pow_of_natCast_mul_mem hi hA)

  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hB
  rcases le_or_gt M'.degree N with hle | hlt
  · rw [(hc M').1 hle, ← hb, mul_comm b, ← mul_assoc, ← pow_add,
      show N - M'.degree + (M'.degree - 1 - K) = N - 1 - K by omega]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rcases (hc M').2 hlt with h | ⟨h, -⟩
    ·
      have h' : (p : 𝓞) ^ (M'.degree - N) * c M' ∈ Ideal.span {(p : 𝓞) ^ (M'.degree - 1 - K)} := by
        rw [mul_comm, h]; exact hB
      have := mem_span_pow_of_pow_mul_mem hpR (by omega) h'
      rwa [show M'.degree - 1 - K - (M'.degree - N) = N - 1 - K by omega] at this
    · rw [h]; exact Ideal.zero_mem _

noncomputable def gam (c : (Fin d →₀ ℕ) → 𝓞) (N k : ℕ) : MvPowerSeries (Fin d) 𝓞 := fun m' => c (p ^ (N - 1 - k) • m')

omit hp in
theorem coeff_gam (c : (Fin d →₀ ℕ) → 𝓞) (N k : ℕ) (m' : Fin d →₀ ℕ) :
    coeff m' (gam (p := p) c N k) = c (p ^ (N - 1 - k) • m') := rfl

theorem gam_succ_sub_expand_mem (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (φi : MvPowerSeries (Fin d) 𝓞)
    (hint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * coeff (m + Finsupp.single j 1) φi ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (N : ℕ) (c : (Fin d →₀ ℕ) → 𝓞)
    (hc : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ N → c m = (p : 𝓞) ^ (N - m.degree) * coeff m φi) ∧
      (N < m.degree → c m * (p : 𝓞) ^ (m.degree - N) = coeff m φi ∨
        (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ coeff m φi)))
    (k : ℕ) (hk : k + 1 < N) :
    gam (p := p) c N (k + 1) - expand p hp.out.ne_zero (gam (p := p) c N k) ∈
      Ideal.span {(p : MvPowerSeries (Fin d) 𝓞) ^ (k + 1)} := by
  apply mem_span_pow_of_forall_coeff_mem
  intro m
  rw [map_sub, coeff_gam]
  by_cases hdiv : ∀ i, p ∣ m i
  ·
    obtain ⟨m₀, rfl⟩ : ∃ m₀ : Fin d →₀ ℕ, m = p • m₀ :=
      ⟨m.mapRange (fun a => a / p) (by simp), by ext i; simp [Nat.mul_div_cancel' (hdiv i)]⟩
    rw [coeff_expand_smul, coeff_gam, smul_smul, ← pow_succ,
      show N - 1 - (k + 1) + 1 = N - 1 - k by omega, sub_self]
    exact Ideal.zero_mem _
  · obtain ⟨i, hi⟩ := not_forall.1 hdiv
    rw [coeff_expand_of_not_dvd p hp.out.ne_zero _ hi, sub_zero]
    have := c_smul_mem hpR φi hint N c hc (N - 1 - (k + 1)) (by omega) m i hi
    rwa [show N - 1 - (N - 1 - (k + 1)) = k + 1 by omega] at this

theorem exists_ell (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (hfrob : ∀ c : 𝓞, c ^ p - c ∈ Ideal.span {(p : 𝓞)})
    (φi : MvPowerSeries (Fin d) 𝓞)
    (hint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * coeff (m + Finsupp.single j 1) φi ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (N : ℕ) (c : (Fin d →₀ ℕ) → 𝓞)
    (hc : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ N → c m = (p : 𝓞) ^ (N - m.degree) * coeff m φi) ∧
      (N < m.degree → c m * (p : 𝓞) ^ (m.degree - N) = coeff m φi ∨
        (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ coeff m φi))) :
    ∃ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞), ∀ n < N, ∀ m' : Fin d →₀ ℕ,
      coeff m' (WittVector.ghostComponent n ℓ) = c (p ^ (N - 1 - n) • m') := by
  obtain ⟨ℓ, hℓ⟩ := WittVector.exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem
    (R := MvPowerSeries (Fin d) 𝓞) p (expand p hp.out.ne_zero).toRingHom
    (fun f => MvPowerSeries.expand_sub_pow_mem_span_natCast p hfrob f) N (gam (p := p) c N)
    (fun k hk => gam_succ_sub_expand_mem hpR φi hint N c hc k hk)
  exact ⟨ℓ, fun n hn m' => by rw [hℓ n hn]; rfl⟩

end S17LCov

universe u v

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hfrob : ∀ c : 𝓞, c ^ p - c ∈ Ideal.span {(p : 𝓞)})
    {d : ℕ} (φi : MvPowerSeries (Fin d) 𝓞)
    (hint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * MvPowerSeries.coeff (m + Finsupp.single j 1) φi ∈
        Ideal.span {(p : 𝓞) ^ m.degree})
    (N : ℕ) (c : (Fin d →₀ ℕ) → 𝓞)
    (hc : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ N → c m = (p : 𝓞) ^ (N - m.degree) * MvPowerSeries.coeff m φi) ∧
      (N < m.degree → c m * (p : 𝓞) ^ (m.degree - N) = MvPowerSeries.coeff m φi ∨
        (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ MvPowerSeries.coeff m φi))) :
    ∃ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞), ∀ n < N, ∀ m' : Fin d →₀ ℕ,
      MvPowerSeries.coeff m' (WittVector.ghostComponent n ℓ) = c (p ^ (N - 1 - n) • m') :=
  S17LCov.exists_ell hp hfrob φi hint N c hc

end S_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_logCovector
end P2MW
export P2MW.S_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_logCovector (solution)
