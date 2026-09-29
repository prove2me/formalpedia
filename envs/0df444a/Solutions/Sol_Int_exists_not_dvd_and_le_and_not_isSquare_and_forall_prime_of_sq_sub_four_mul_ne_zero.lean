-- Prove2me | solution 1 for Int.exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/832a4770-5ec4-517d-bf70-d70149e5c5b3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Int_exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero

set_option autoImplicit false

namespace Int
p2m_export "Int" "natAbs_sq sq_mod_four_eq_one_of_odd natAbs emod_eq_zero_of_dvd natAbs_dvd_natAbs natCast_natAbs toNat_of_nonneg even_or_odd one_le_abs natAbs_natCast toNat natAbs_ne_zero associated_iff_natAbs prime_two"
namespace DeuringNormalisation
p2m_open "Int"

def g (t q a : ℤ) : ℤ := a ^ 2 + t * a + q

theorem g_sub (t q a r : ℤ) : g t q a - g t q r = (a - r) * (a + r + t) := by
  unfold g; ring

theorem four_mul_g (t q a : ℤ) : 4 * g t q a = (2 * a + t) ^ 2 - (t ^ 2 - 4 * q) := by
  unfold g; ring

theorem dvd_g_sub_of_dvd_sub {n t q a r : ℤ} (h : n ∣ a - r) : n ∣ g t q a - g t q r := by
  rw [g_sub]; exact Dvd.dvd.mul_right h _

theorem not_isSquare_of_sq_lt_of_lt_sq {N : ℤ} {u : ℕ} (h1 : (u : ℤ) ^ 2 < N)
    (h2 : N < ((u : ℤ) + 1) ^ 2) : ¬ IsSquare N := by
  rintro ⟨r, hr⟩
  have hN : N = (r.natAbs : ℤ) ^ 2 := by rw [Int.natAbs_sq, sq]; exact hr
  rw [hN] at h1 h2
  have h1' : u ^ 2 < r.natAbs ^ 2 := by exact_mod_cast h1
  have h2' : r.natAbs ^ 2 < (u + 1) ^ 2 := by exact_mod_cast h2
  exact Nat.not_exists_sq' h1' h2' ⟨r.natAbs, rfl⟩

theorem not_isSquare_of_four_mul {N : ℤ} (h : ¬ IsSquare (4 * N)) : ¬ IsSquare N := by
  rintro ⟨r, hr⟩
  exact h ⟨2 * r, by rw [hr]; ring⟩

theorem two_dvd_of_four_dvd_sq {t : ℤ} (h : (4 : ℤ) ∣ t ^ 2) : (2 : ℤ) ∣ t := by
  rcases Int.even_or_odd t with ht | ht
  · exact even_iff_two_dvd.mp ht
  · exfalso
    have h1 := Int.sq_mod_four_eq_one_of_odd ht
    have h2 : t ^ 2 % 4 = 0 := Int.emod_eq_zero_of_dvd h
    omega

def rOdd (t : ℤ) (ℓ : ℕ) : ℤ := if (ℓ : ℤ) ∣ t then 1 else 0

theorem not_dvd_two_mul_rOdd_add {t : ℤ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) :
    ¬ (ℓ : ℤ) ∣ 2 * rOdd t ℓ + t := by
  unfold rOdd
  split_ifs with h
  · intro h2
    have h3 : (ℓ : ℤ) ∣ 2 := by
      have : (ℓ : ℤ) ∣ (2 * 1 + t) - t := dvd_sub h2 h
      simpa using this
    have h4 : ℓ ∣ 2 := by exact_mod_cast h3
    have := (Nat.prime_two.eq_one_or_self_of_dvd ℓ h4)
    rcases this with h5 | h5
    · exact hℓ.one_lt.ne' h5
    · exact hℓ2 h5
  · simpa using h

def rFour (q : ℤ) : ℤ := if (2 : ℤ) ∣ q then 1 else 0

theorem not_two_dvd_g_rFour {t q : ℤ} (ht : (2 : ℤ) ∣ t) : ¬ (2 : ℤ) ∣ g t q (rFour q) := by
  unfold rFour g
  split_ifs with h
  · intro h2
    have h3 : (2 : ℤ) ∣ (1 ^ 2 + t * 1 + q) - t - q := dvd_sub (dvd_sub h2 (by simpa using ht)) h
    have e : (1 : ℤ) ^ 2 + t * 1 + q - t - q = 1 := by ring
    rw [e] at h3
    norm_num at h3
  · simpa using h

def xf (t q : ℤ) (p : ℕ) (a₀ : ℤ) (ℓ : ℕ) : ℤ :=
  if ℓ = p then a₀ else if ℓ = 2 then rFour q else rOdd t ℓ

def ef (ℓ : ℕ) : ℕ := if ℓ = 2 then 2 else 1

def primeSet (D : ℤ) (p : ℕ) : Finset ℕ :=
  insert p (insert 2 ((D.natAbs.primeFactors).filter (fun ℓ => ℓ ≠ p ∧ ℓ ≠ 2)))

theorem prime_of_mem_primeSet {D : ℤ} {p : ℕ} (hp : p.Prime) {ℓ : ℕ} (h : ℓ ∈ primeSet D p) :
    ℓ.Prime := by
  unfold primeSet at h
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_filter] at h
  rcases h with rfl | rfl | ⟨h, -⟩
  · exact hp
  · exact Nat.prime_two
  · exact (Nat.mem_primeFactors.mp h).1

theorem mem_primeSet_of_dvd {D : ℤ} (hD : D ≠ 0) {p ℓ : ℕ} (hℓ : ℓ.Prime) (hdvd : (ℓ : ℤ) ∣ D) :
    ℓ ∈ primeSet D p := by
  unfold primeSet
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_filter]
  by_cases h1 : ℓ = p
  · exact Or.inl h1
  by_cases h2 : ℓ = 2
  · exact Or.inr (Or.inl h2)
  refine Or.inr (Or.inr ⟨?_, h1, h2⟩)
  rw [Nat.mem_primeFactors]
  refine ⟨hℓ, ?_, Int.natAbs_ne_zero.mpr hD⟩
  have := Int.natAbs_dvd_natAbs.mpr hdvd
  rwa [Int.natAbs_natCast] at this

theorem exists_forall_dvd_sub_xf (t q : ℤ) (D : ℤ) (p : ℕ) (hp : p.Prime) (a₀ : ℤ) :
    ∃ y : ℤ, ∀ ℓ ∈ primeSet D p, ((ℓ : ℤ) ^ ef ℓ) ∣ y - xf t q p a₀ ℓ := by
  classical
  have hprime : ∀ ℓ ∈ primeSet D p, Prime (Ideal.span {(ℓ : ℤ)}) := by
    intro ℓ hℓ
    have hℓp := prime_of_mem_primeSet hp hℓ
    have hne : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓp.ne_zero
    refine Ideal.prime_of_isPrime ?_ ((Ideal.span_singleton_prime hne).mpr
      (Nat.prime_iff_prime_int.mp hℓp))
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  have hne : ∀ ℓ ∈ primeSet D p, ∀ ℓ' ∈ primeSet D p, ℓ ≠ ℓ' →
      Ideal.span {(ℓ : ℤ)} ≠ Ideal.span {(ℓ' : ℤ)} := by
    intro ℓ _ ℓ' _ hne h
    apply hne
    have := Ideal.span_singleton_eq_span_singleton.mp h
    rw [Int.associated_iff_natAbs, Int.natAbs_natCast, Int.natAbs_natCast] at this
    exact this
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := primeSet D p) (fun ℓ => Ideal.span {(ℓ : ℤ)}) ef hprime hne
    (fun ℓ => xf t q p a₀ ℓ.1)
  refine ⟨y, fun ℓ hℓ => ?_⟩
  have h := hy ℓ hℓ
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  exact h

section Verify

variable {t q : ℤ} {p : ℕ} {a₀ a : ℤ}

theorem not_dvd_g (ha₀ : ¬ (p : ℤ) ∣ g t q a₀) (h : (p : ℤ) ∣ a - a₀) : ¬ (p : ℤ) ∣ g t q a := by
  intro h2
  apply ha₀
  have h3 : (p : ℤ) ∣ g t q a - g t q a₀ := dvd_g_sub_of_dvd_sub h
  have := dvd_sub h2 h3
  simpa using this

theorem primitive (hp : p.Prime) (hD : t ^ 2 - 4 * q ≠ 0)
    (hpg : ¬ (p : ℤ) ∣ g t q a)
    (hcong : ∀ ℓ ∈ primeSet (t ^ 2 - 4 * q) p, ((ℓ : ℤ) ^ ef ℓ) ∣ a - xf t q p a₀ ℓ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (h1 : (ℓ : ℤ) ∣ 2 * a + t) (h2 : (ℓ : ℤ) ^ 2 ∣ g t q a) : False := by

  have hD2 : (ℓ : ℤ) ^ 2 ∣ t ^ 2 - 4 * q := by
    have e : t ^ 2 - 4 * q = (2 * a + t) ^ 2 - 4 * g t q a := by rw [four_mul_g]; ring
    rw [e]
    exact dvd_sub (pow_dvd_pow_of_dvd h1 2) (Dvd.dvd.mul_left h2 4)
  have hD1 : (ℓ : ℤ) ∣ t ^ 2 - 4 * q := (dvd_pow_self (ℓ : ℤ) two_ne_zero).trans hD2
  have hmem : ℓ ∈ primeSet (t ^ 2 - 4 * q) p := mem_primeSet_of_dvd hD hℓ hD1
  have hc := hcong ℓ hmem

  by_cases hℓp : ℓ = p
  · subst hℓp
    exact hpg ((dvd_pow_self (ℓ : ℤ) two_ne_zero).trans h2)

  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    have hx : xf t q p a₀ 2 = rFour q := by
      unfold xf; rw [if_neg hℓp, if_pos rfl]
    have he : ef 2 = 2 := by unfold ef; rw [if_pos rfl]
    rw [hx, he] at hc
    push_cast at hc h2 hD2 h1

    have ht : (2 : ℤ) ∣ t := by
      have h4 : (4 : ℤ) ∣ t ^ 2 := by
        have : (4 : ℤ) ∣ (t ^ 2 - 4 * q) + 4 * q := dvd_add (by simpa using hD2) (dvd_mul_right 4 q)
        simpa using this
      exact two_dvd_of_four_dvd_sq h4

    have h5 : (4 : ℤ) ∣ g t q a - g t q (rFour q) := dvd_g_sub_of_dvd_sub (by simpa using hc)
    have h6 : (2 : ℤ) ∣ g t q (rFour q) := by
      have h7 : (2 : ℤ) ∣ g t q a := (show (2 : ℤ) ∣ 4 by norm_num).trans (by simpa using h2)
      have h8 : (2 : ℤ) ∣ g t q a - g t q (rFour q) := (show (2 : ℤ) ∣ 4 by norm_num).trans h5
      have := dvd_sub h7 h8
      simpa using this
    exact not_two_dvd_g_rFour ht h6

  · have hx : xf t q p a₀ ℓ = rOdd t ℓ := by
      unfold xf; rw [if_neg hℓp, if_neg hℓ2]
    have he : ef ℓ = 1 := by unfold ef; rw [if_neg hℓ2]
    rw [hx, he, pow_one] at hc
    have h3 : (ℓ : ℤ) ∣ 2 * rOdd t ℓ + t := by
      have h4 : (ℓ : ℤ) ∣ 2 * (a - rOdd t ℓ) := Dvd.dvd.mul_left hc 2
      have := dvd_sub h1 h4
      have e : 2 * a + t - 2 * (a - rOdd t ℓ) = 2 * rOdd t ℓ + t := by ring
      rwa [e] at this
    exact not_dvd_two_mul_rOdd_add hℓ hℓ2 h3

end Verify

theorem two_le_and_not_isSquare {t q a : ℤ} (hD : t ^ 2 - 4 * q ≠ 0)
    (hu : |t ^ 2 - 4 * q| + 2 ≤ 2 * a + t) : 2 ≤ g t q a ∧ ¬ IsSquare (g t q a) := by
  set D := t ^ 2 - 4 * q with hDdef
  set u := 2 * a + t with hudef
  have h4g : 4 * g t q a = u ^ 2 - D := four_mul_g t q a
  have hu0 : 0 ≤ u := by have := abs_nonneg D; omega
  have habs : |D| + 2 ≤ u := hu
  constructor
  ·
    have hDu : D ≤ u := by linarith [le_abs_self D]
    have hnegDu : -D ≤ u := by linarith [neg_abs_le D, abs_nonneg D]
    have hu3 : 3 ≤ u := by linarith [abs_nonneg D, Int.one_le_abs hD]
    have h6 : 6 ≤ 4 * g t q a := by rw [h4g]; nlinarith
    omega
  ·
    apply not_isSquare_of_four_mul
    rw [h4g]
    rcases lt_or_gt_of_ne hD with hDneg | hDpos
    ·
      have hDabs : -D = |D| := (abs_of_neg hDneg).symm
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = u := ⟨u.toNat, Int.toNat_of_nonneg hu0⟩
      refine not_isSquare_of_sq_lt_of_lt_sq (u := n) ?_ ?_
      · rw [hn]; linarith
      · rw [hn]; nlinarith
    ·
      have hDabs : D = |D| := (abs_of_pos hDpos).symm
      have hu1 : 1 ≤ u := by linarith [abs_nonneg D]
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = u - 1 :=
        ⟨(u - 1).toNat, Int.toNat_of_nonneg (by linarith)⟩
      refine not_isSquare_of_sq_lt_of_lt_sq (u := n) ?_ ?_
      · rw [hn]; nlinarith
      · rw [hn]; nlinarith

theorem main (t q : ℤ) (hD : t ^ 2 - 4 * q ≠ 0) (p : ℕ) (hp : p.Prime) (a₀ : ℤ)
    (ha₀ : ¬ (p : ℤ) ∣ a₀ ^ 2 + t * a₀ + q) :
    ∃ a : ℤ, ¬ (p : ℤ) ∣ a ^ 2 + t * a + q ∧ 2 ≤ a ^ 2 + t * a + q ∧
      ¬ IsSquare (a ^ 2 + t * a + q) ∧
      ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ 2 * a + t → ¬ (ℓ : ℤ) ^ 2 ∣ a ^ 2 + t * a + q := by
  set D := t ^ 2 - 4 * q with hDdef

  obtain ⟨y, hy⟩ := exists_forall_dvd_sub_xf t q D p hp a₀

  set M : ℤ := 4 * p * |D| with hMdef
  have hM1 : 1 ≤ M := by
    have h1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.one_lt.le
    have h2 : 1 ≤ |D| := Int.one_le_abs hD
    nlinarith
  set k : ℤ := |2 * y + t| + |D| + 2 with hkdef
  have hk0 : 0 ≤ k := by positivity
  set a : ℤ := y + k * M with hadef
  have hcong : ∀ ℓ ∈ primeSet D p, ((ℓ : ℤ) ^ ef ℓ) ∣ a - xf t q p a₀ ℓ := by
    intro ℓ hℓ
    have hℓM : ((ℓ : ℤ) ^ ef ℓ) ∣ M := by
      unfold primeSet at hℓ
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_filter] at hℓ
      by_cases h2 : ℓ = 2
      · subst h2
        have he : ef 2 = 2 := by unfold ef; rw [if_pos rfl]
        rw [he]
        exact ⟨p * |D|, by push_cast; ring⟩
      · have he : ef ℓ = 1 := by unfold ef; rw [if_neg h2]
        rw [he, pow_one]
        rcases hℓ with rfl | rfl | ⟨hℓ, -, -⟩
        · exact ⟨4 * |D|, by ring⟩
        · exact absurd rfl h2
        · have hℓD : (ℓ : ℤ) ∣ |D| := by
            rw [← Int.natCast_natAbs]
            exact_mod_cast (Nat.mem_primeFactors.mp hℓ).2.1
          exact hℓD.mul_left _
    have e : a - xf t q p a₀ ℓ = (y - xf t q p a₀ ℓ) + k * M := by rw [hadef]; ring
    rw [e]
    exact dvd_add (hy ℓ hℓ) (hℓM.mul_left k)

  have hpmem : p ∈ primeSet D p := by unfold primeSet; exact Finset.mem_insert_self _ _
  have hpa : (p : ℤ) ∣ a - a₀ := by
    have h := hcong p hpmem
    have hx : xf t q p a₀ p = a₀ := by unfold xf; rw [if_pos rfl]
    rw [hx] at h
    exact (dvd_pow_self (p : ℤ) (by unfold ef; split_ifs <;> norm_num)).trans h
  have hpg : ¬ (p : ℤ) ∣ g t q a := not_dvd_g ha₀ hpa

  have hu : |D| + 2 ≤ 2 * a + t := by
    have e : 2 * a + t = (2 * y + t) + 2 * k * M := by rw [hadef]; ring
    rw [e]
    have h1 : k ≤ k * M := by nlinarith
    have h2 : -|2 * y + t| ≤ 2 * y + t := neg_abs_le _
    nlinarith [abs_nonneg (2 * y + t), abs_nonneg D]
  obtain ⟨h2, hsq⟩ := two_le_and_not_isSquare hD hu
  refine ⟨a, hpg, h2, hsq, fun ℓ hℓ h1 h3 => ?_⟩
  exact primitive hp hD hpg hcong ℓ hℓ h1 h3

end Int.DeuringNormalisation

theorem solution (t q : ℤ) (hD : t ^ 2 - 4 * q ≠ 0) (p : ℕ) [Fact p.Prime] (h : ∃ a₀ : ℤ, ¬ (p : ℤ) ∣ a₀ ^ 2 + t * a₀ + q) : ∃ a : ℤ, ¬ (p : ℤ) ∣ a ^ 2 + t * a + q ∧ 2 ≤ a ^ 2 + t * a + q ∧ ¬ IsSquare (a ^ 2 + t * a + q) ∧ ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ 2 * a + t → ¬ (ℓ : ℤ) ^ 2 ∣ a ^ 2 + t * a + q := by
  obtain ⟨a₀, ha₀⟩ := h
  exact Int.DeuringNormalisation.main t q hD p (Fact.out) a₀ ha₀

end S_Int_exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero
end P2MW
export P2MW.S_Int_exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero (solution)
