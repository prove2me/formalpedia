-- Prove2me | solution 1 for LSeries.exists_hasProd_tsum_eq_lseries_of_norm_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e3512901-61c1-561b-9c62-7e780d41b22f

import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LSeries_exists_hasProd_tsum_eq_lseries_of_norm_le_pow

set_option autoImplicit false

open scoped ComplexOrder
open scoped Classical

noncomputable section

namespace RS11G2

open Complex Finset

variable {ι : Type*} (N : ι → ℕ) (E : ι → ℕ → ℂ)

def loc (p k : ℕ) : ℂ :=
  if h : ∃ i, N i = p then E h.choose k else (if k = 0 then 1 else 0)

def coeff (n : ℕ) : ℂ := n.factorization.prod fun p k => loc N E p k

variable {N E}

theorem loc_N (hinj : Function.Injective N) (i : ι) (k : ℕ) : loc N E (N i) k = E i k := by
  have h : ∃ j, N j = N i := ⟨i, rfl⟩
  rw [loc, dif_pos h, hinj h.choose_spec]

theorem loc_zero (hE0 : ∀ i, E i 0 = 1) (p : ℕ) : loc N E p 0 = 1 := by
  unfold loc
  by_cases h : ∃ i, N i = p
  · rw [dif_pos h]; exact hE0 _
  · rw [dif_neg h, if_pos rfl]

theorem loc_of_not (p k : ℕ) (h : ¬ ∃ i, N i = p) (hk : k ≠ 0) : loc N E p k = 0 := by
  rw [loc, dif_neg h, if_neg hk]

theorem coeff_zero : coeff N E 0 = 1 := by simp [coeff]

theorem coeff_one : coeff N E 1 = 1 := by simp [coeff]

theorem coeff_prime_pow (hE0 : ∀ i, E i 0 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    coeff N E (p ^ k) = loc N E p k := by
  rw [coeff, hp.factorization_pow, Finsupp.prod_single_index (loc_zero hE0 p)]

theorem coeff_N_pow (hN : ∀ i, (N i).Prime) (hinj : Function.Injective N) (hE0 : ∀ i, E i 0 = 1)
    (i : ι) (k : ℕ) : coeff N E (N i ^ k) = E i k := by
  rw [coeff_prime_pow hE0 (hN i), loc_N hinj]

theorem coeff_mul_of_coprime {m n : ℕ} (hmn : Nat.Coprime m n) :
    coeff N E (m * n) = coeff N E m * coeff N E n := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn; subst hmn; simp [coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn; subst hmn; simp [coeff_one]
  rw [coeff, Nat.factorization_mul hm hn, Finsupp.prod_add_index_of_disjoint]
  · rfl
  · rw [Nat.support_factorization, Nat.support_factorization]
    exact hmn.disjoint_primeFactors

theorem norm_loc_le (hN : ∀ i, (N i).Prime) (hinj : Function.Injective N) (hE0 : ∀ i, E i 0 = 1)
    (A : ℝ) (hEA : ∀ i k, ‖E i k‖ ≤ (((N i : ℝ) ^ k) ^ A)) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ‖loc N E p k‖ ≤ (((p : ℝ) ^ k) ^ A) := by
  by_cases h : ∃ i, N i = p
  · obtain ⟨i, rfl⟩ := h
    rw [loc_N hinj]; exact hEA i k
  · by_cases hk : k = 0
    · subst hk; rw [loc_zero hE0]; simp
    · rw [loc_of_not p k h hk, norm_zero]
      exact Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _

theorem norm_coeff_le (hN : ∀ i, (N i).Prime) (hinj : Function.Injective N) (hE0 : ∀ i, E i 0 = 1)
    (A : ℝ) (hEA : ∀ i k, ‖E i k‖ ≤ (((N i : ℝ) ^ k) ^ A)) :
    ∀ n : ℕ, n ≠ 0 → ‖coeff N E n‖ ≤ (n : ℝ) ^ A := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd rfl h
  | one => intro _; simp [coeff_one]
  | prime_pow p k hp hk =>
    intro _
    rw [coeff_prime_pow hE0 hp]
    have := norm_loc_le hN hinj hE0 A hEA hp k
    push_cast
    exact this
  | coprime a b ha hb hab iha ihb =>
    intro _
    rw [coeff_mul_of_coprime hab, norm_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact mul_le_mul (iha (by omega)) (ihb (by omega)) (norm_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem loc_nonneg (hpos : ∀ i k, 0 ≤ E i k) (p k : ℕ) : 0 ≤ loc N E p k := by
  unfold loc
  by_cases h : ∃ i, N i = p
  · rw [dif_pos h]; exact hpos _ _
  · rw [dif_neg h]
    by_cases hk : k = 0
    · rw [if_pos hk]; exact zero_le_one
    · rw [if_neg hk]

theorem coeff_nonneg (hpos : ∀ i k, 0 ≤ E i k) (n : ℕ) : 0 ≤ coeff N E n := by
  unfold coeff Finsupp.prod
  exact Finset.prod_nonneg fun p _ => loc_nonneg hpos p _

theorem natCast_pow_cpow (n k : ℕ) (s : ℂ) : (((n ^ k : ℕ)) : ℂ) ^ s = ((n : ℂ) ^ s) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.cast_mul, natCast_mul_natCast_cpow, ih, pow_succ]

theorem term_mul_of_coprime (s : ℂ) {m n : ℕ} (hmn : Nat.Coprime m n) :
    LSeries.term (coeff N E) s (m * n) = LSeries.term (coeff N E) s m * LSeries.term (coeff N E) s n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [LSeries.term_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  rw [LSeries.term_of_ne_zero (mul_ne_zero hm hn), LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn,
    coeff_mul_of_coprime hmn, Nat.cast_mul, natCast_mul_natCast_cpow]
  field_simp

theorem tsum_term_N_pow (hN : ∀ i, (N i).Prime) (hinj : Function.Injective N) (hE0 : ∀ i, E i 0 = 1)
    (s : ℂ) (i : ι) :
    ∑' k : ℕ, LSeries.term (coeff N E) s (N i ^ k) = ∑' k : ℕ, E i k * (((N i : ℕ) : ℂ) ^ (-s)) ^ k := by
  refine tsum_congr fun k => ?_
  have hne : N i ^ k ≠ 0 := pow_ne_zero _ (hN i).ne_zero
  rw [LSeries.term_of_ne_zero hne, coeff_N_pow hN hinj hE0, natCast_pow_cpow, cpow_neg, inv_pow,
    div_eq_mul_inv]

theorem tsum_term_pow_of_not (hE0 : ∀ i, E i 0 = 1) (s : ℂ) {p : ℕ} (hp : p.Prime)
    (h : ¬ ∃ i, N i = p) : ∑' k : ℕ, LSeries.term (coeff N E) s (p ^ k) = 1 := by
  rw [tsum_eq_single 0]
  · rw [pow_zero, LSeries.term_of_ne_zero one_ne_zero, coeff_one]; simp
  · intro k hk
    rw [LSeries.term_of_ne_zero (pow_ne_zero _ hp.ne_zero), coeff_prime_pow hE0 hp, loc_of_not p k h hk,
      zero_div]

end RS11G2

open RS11G2 in

theorem solution
    {ι : Type*} (N : ι → ℕ) (hN : ∀ i : ι, (N i).Prime) (hinj : Function.Injective N)
    (E : ι → ℕ → ℂ) (hE0 : ∀ i : ι, E i 0 = 1) (A : ℝ)
    (hEA : ∀ (i : ι) (k : ℕ), ‖E i k‖ ≤ (((N i : ℝ) ^ k) ^ A)) :
    ∃ c : ℕ → ℂ,
      (∀ (i : ι) (k : ℕ), c (N i ^ k) = E i k) ∧
      ((∀ (i : ι) (k : ℕ), 0 ≤ E i k) → 0 ≤ c) ∧
      LSeries.abscissaOfAbsConv c ≤ ((A + 1 : ℝ) : EReal) ∧
      ∀ s : ℂ, A + 1 < s.re →
        HasProd (fun i : ι => ∑' k : ℕ, E i k * (((N i : ℕ) : ℂ) ^ (-s)) ^ k) (LSeries c s) := by
  refine ⟨coeff N E, coeff_N_pow hN hinj hE0, fun hpos => fun n => coeff_nonneg hpos n, ?_, ?_⟩
  · exact LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
      ⟨1, fun n hn => by rw [one_mul]; exact norm_coeff_le hN hinj hE0 A hEA n hn⟩
  · intro s hs
    have hsum : LSeriesSummable (coeff N E) s :=
      LSeriesSummable_of_le_const_mul_rpow (x := A + 1) hs
        ⟨1, fun n hn => by rw [one_mul, add_sub_cancel_right]; exact norm_coeff_le hN hinj hE0 A hEA n hn⟩
    have hsumn : Summable fun n => ‖LSeries.term (coeff N E) s n‖ := summable_norm_iff.mpr hsum
    have hEP := EulerProduct.eulerProduct_hasProd (f := LSeries.term (coeff N E) s)
      (by rw [LSeries.term_of_ne_zero one_ne_zero, coeff_one]; simp)
      (fun hmn => term_mul_of_coprime s hmn) hsumn (LSeries.term_zero _ _)

    set φ : ι → Nat.Primes := fun i => ⟨N i, hN i⟩ with hφ
    have hφinj : Function.Injective φ := fun i j h => hinj (by
      have := congrArg Subtype.val h; exact this)
    have hout : ∀ p : Nat.Primes, p ∉ Set.range φ →
        (fun p : Nat.Primes => ∑' e : ℕ, LSeries.term (coeff N E) s (p ^ e)) p = 1 := by
      intro p hp
      apply tsum_term_pow_of_not hE0 s p.2
      rintro ⟨i, hi⟩
      exact hp ⟨i, Subtype.ext hi⟩
    have h2 := (hφinj.hasProd_iff hout).mpr hEP
    have h3 : ((fun p : Nat.Primes => ∑' e : ℕ, LSeries.term (coeff N E) s (p ^ e)) ∘ φ) =
        fun i : ι => ∑' k : ℕ, E i k * (((N i : ℕ) : ℂ) ^ (-s)) ^ k := by
      funext i
      simp only [Function.comp_apply, hφ]
      exact tsum_term_N_pow hN hinj hE0 s i
    rw [h3] at h2
    exact h2

end
end S_LSeries_exists_hasProd_tsum_eq_lseries_of_norm_le_pow
end P2MW
export P2MW.S_LSeries_exists_hasProd_tsum_eq_lseries_of_norm_le_pow (solution)
