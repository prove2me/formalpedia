-- Prove2me | solution 1 for LiouvilleDiffAlg.ratFunc_pole_free
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T11:43:02.760253+00:00
-- url     : https://prove2.me/submissions/00c696a6-e412-4e30-9232-a0b04a9118ec

import Mathlib

open scoped Differential
open Polynomial

theorem solution {K : Type*} [Field K] [Differential K] [CharZero K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    (hpoly : ∀ r : K[X], ∃ q : K[X], (algebraMap K[X] (RatFunc K) r)′ = algebraMap K[X] (RatFunc K) q)
    {p q : K[X]} (hp : Irreducible p) (hq : (algebraMap K[X] (RatFunc K) p)′ = algebraMap K[X] (RatFunc K) q)
    (hpq : ¬ p ∣ q) (x : RatFunc K)
    (hx : ∃ r s : K[X], ¬ p ∣ s ∧ x′ * algebraMap K[X] (RatFunc K) (p * s) = algebraMap K[X] (RatFunc K) r) :
    ∃ a b : K[X], ¬ p ∣ b ∧ x * algebraMap K[X] (RatFunc K) b = algebraMap K[X] (RatFunc K) a := by
  obtain ⟨r, s, hs, hxrs⟩ := hx
  have hinj := RatFunc.algebraMap_injective K
  have hxe : x * algebraMap K[X] (RatFunc K) x.denom = algebraMap K[X] (RatFunc K) x.num := by
    have h1 := RatFunc.num_div_denom x
    have h2 : algebraMap K[X] (RatFunc K) x.denom ≠ 0 :=
      RatFunc.algebraMap_ne_zero x.denom_ne_zero
    calc x * algebraMap K[X] (RatFunc K) x.denom
        = (algebraMap K[X] (RatFunc K) x.num / algebraMap K[X] (RatFunc K) x.denom) *
            algebraMap K[X] (RatFunc K) x.denom := by rw [h1]
      _ = _ := div_mul_cancel₀ _ h2
  by_cases hb : p ∣ x.denom
  swap
  · exact ⟨x.num, x.denom, hb, hxe⟩
  exfalso
  obtain ⟨m, b', hnd, hb0⟩ := WfDvdMonoid.max_power_factor x.denom_ne_zero hp
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := by
    rcases m with _ | n
    · exfalso; apply hnd; simpa [hb0] using hb
    · exact ⟨n, rfl⟩
  have hpa : ¬ p ∣ x.num := fun h =>
    hp.not_isUnit ((RatFunc.isCoprime_num_denom x).isUnit_of_dvd' h hb)
  obtain ⟨qa, hqa⟩ := hpoly x.num
  obtain ⟨qb, hqb⟩ := hpoly b'
  set ι := algebraMap K[X] (RatFunc K) with hι
  set P := ι p with hP
  set B := ι b' with hB
  set A := ι x.num with hA
  have h1 : x * (P ^ (n + 1) * B) = A := by
    rw [← hxe, hb0, map_mul, map_pow]
  have h2 := congrArg (fun z => z′) h1
  simp only [Derivation.leibniz, Derivation.leibniz_pow, hq, hqa, hqb, smul_eq_mul,
    nsmul_eq_mul] at h2
  have h3 : x′ * (P ^ (n + 2) * B ^ 2) =
      (ι qa * B - A * ι qb) * P - ((n + 1 : ℕ) : RatFunc K) * A * ι q * B := by
    simp only [Nat.add_sub_cancel] at h2
    linear_combination (P * B) * h2 - (((n + 1 : ℕ) : RatFunc K) * ι q * B + P * ι qb) * h1
  have h4 : ι (s * (((qa * b' - x.num * qb) * p - ((n + 1 : ℕ) : K[X]) * x.num * q * b')))
      = ι (r * p ^ (n + 1) * b' ^ 2) := by
    simp only [map_mul, map_sub, map_pow, map_natCast, ← hP, ← hB, ← hA]
    have := hxrs
    simp only [map_mul, ← hP] at this
    linear_combination (-(ι s)) * h3 + (P ^ (n + 1) * B ^ 2) * this
  have h5 := hinj h4
  have hpr := hp.prime
  have h6 : p ∣ s * (((qa * b' - x.num * qb) * p - ((n + 1 : ℕ) : K[X]) * x.num * q * b')) := by
    rw [h5]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self p (Nat.succ_ne_zero n)) _) _
  rcases hpr.dvd_or_dvd h6 with h7 | h7
  · exact hs h7
  · have h8 : p ∣ ((n + 1 : ℕ) : K[X]) * x.num * q * b' := by
      have : p ∣ (qa * b' - x.num * qb) * p := dvd_mul_left _ _
      have h9 := (dvd_sub this h7)
      simpa using h9
    have hn : ((n + 1 : ℕ) : K[X]) = C ((n + 1 : ℕ) : K) := by simp
    rcases hpr.dvd_or_dvd h8 with h9 | h9
    · rcases hpr.dvd_or_dvd h9 with h10 | h10
      · rcases hpr.dvd_or_dvd h10 with h11 | h11
        · rw [hn] at h11
          have hne : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
          exact hp.not_isUnit (isUnit_of_dvd_unit h11 (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hne)))
        · exact hpa h11
      · exact hpq h10
    · exact hnd h9
