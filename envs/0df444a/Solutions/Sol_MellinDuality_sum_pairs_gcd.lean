-- Prove2me | solution 1 for MellinDuality.sum_pairs_gcd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:51:11.114912+00:00
-- url     : https://prove2.me/submissions/f03ea398-9f55-42c9-819f-df90ca36b728

module
public import Definitions.Def_MellinDuality_Quartic
public import Definitions.Def_MellinDuality_Parseval
public import Definitions.Def_MellinDuality_Pairs
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
attribute [local simp] MellinDuality.gi_im
attribute [local simp] MellinDuality.gi_re



set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
namespace MellinDuality
theorem _root_.solution {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → M) :
    ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, F n n' =
      ∑ ab ∈ coprimePairs N, ∑ r ∈ pairRange N ab, F (ab.1 * r) (ab.2 * r) := by
  rw [← sum_product' (f := F), sum_sigma']
  symm
  refine sum_nbij' (fun x => (x.1.1 * x.2, x.1.2 * x.2))
    (fun y => ⟨(y.1 / Nat.gcd y.1 y.2, y.2 / Nat.gcd y.1 y.2), Nat.gcd y.1 y.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, r⟩ h
    simp only [coprimePairs, pairRange, mem_sigma, mem_filter, mem_product,
      mem_Icc] at h
    obtain ⟨⟨⟨⟨ha1, haN⟩, hb1, hbN⟩, -⟩, hr1, hrK⟩ := h
    have hmax : max a b * (N / max a b) ≤ N := Nat.mul_div_le N (max a b)
    have hra : a * r ≤ max a b * (N / max a b) :=
      Nat.mul_le_mul (le_max_left a b) hrK
    have hrb : b * r ≤ max a b * (N / max a b) :=
      Nat.mul_le_mul (le_max_right a b) hrK
    simp only [mem_product, mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.2 (by positivity), by omega⟩,
      ⟨Nat.one_le_iff_ne_zero.2 (by positivity), by omega⟩⟩
  · rintro ⟨n, n'⟩ h
    simp only [mem_product, mem_Icc] at h
    obtain ⟨⟨hn1, hnN⟩, hn'1, hn'N⟩ := h
    have hg : 0 < Nat.gcd n n' := Nat.gcd_pos_of_pos_left _ (by omega)
    have hdn : Nat.gcd n n' ∣ n := Nat.gcd_dvd_left n n'
    have hdn' : Nat.gcd n n' ∣ n' := Nat.gcd_dvd_right n n'
    have e1 : n / Nat.gcd n n' * Nat.gcd n n' = n := Nat.div_mul_cancel hdn
    have e2 : n' / Nat.gcd n n' * Nat.gcd n n' = n' := Nat.div_mul_cancel hdn'
    have hq1 : 1 ≤ n / Nat.gcd n n' := Nat.div_pos (Nat.le_of_dvd (by omega) hdn) hg
    have hq2 : 1 ≤ n' / Nat.gcd n n' := Nat.div_pos (Nat.le_of_dvd (by omega) hdn') hg
    have hq1N : n / Nat.gcd n n' ≤ N := (Nat.div_le_self _ _).trans hnN
    have hq2N : n' / Nat.gcd n n' ≤ N := (Nat.div_le_self _ _).trans hn'N
    simp only [coprimePairs, pairRange, mem_sigma, mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨⟨hq1, hq1N⟩, hq2, hq2N⟩, Nat.coprime_div_gcd_div_gcd hg⟩, hg, ?_⟩
    rw [Nat.le_div_iff_mul_le (lt_of_lt_of_le zero_lt_one (le_max_of_le_left hq1))]
    rcases le_total (n / Nat.gcd n n') (n' / Nat.gcd n n') with h | h
    · rw [max_eq_right h, mul_comm, e2]; exact hn'N
    · rw [max_eq_left h, mul_comm, e1]; exact hnN
  · rintro ⟨⟨a, b⟩, r⟩ h
    simp only [coprimePairs, pairRange, mem_sigma, mem_filter, mem_product,
      mem_Icc] at h
    obtain ⟨⟨⟨⟨ha1, -⟩, hb1, -⟩, hab⟩, hr1, -⟩ := h
    have hgcd : Nat.gcd (a * r) (b * r) = r := by
      rw [Nat.gcd_mul_right, hab, one_mul]
    simp only [hgcd, Nat.mul_div_cancel _ (show 0 < r by omega)]
  · rintro ⟨n, n'⟩ _
    simp only [Nat.div_mul_cancel (Nat.gcd_dvd_left n n'),
      Nat.div_mul_cancel (Nat.gcd_dvd_right n n')]
  · rintro ⟨⟨a, b⟩, r⟩ _; rfl
end MellinDuality
