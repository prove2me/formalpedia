-- Prove2me | solution 1 for KadatchJenkins.X_pow_mod_eq_prod_pow2k
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T10:13:28.763894+00:00
-- url     : https://prove2.me/submissions/ff11bc23-0c02-4c90-ac9f-32d1b9e5b029

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkinsS4a

theorem modmod (P a : (ZMod 2)[X]) : a % P % P = a % P := by
  by_cases hP : P = 0
  · subst hP; simp
  · exact (Polynomial.mod_eq_self_iff hP).2 (Polynomial.degree_mod_lt a hP)

theorem mulmod (P a b : (ZMod 2)[X]) : (a % P * b) % P = (a * b) % P := by
  rw [Polynomial.mul_mod, Polynomial.mul_mod a b, modmod]

theorem prod_mod (P : (ZMod 2)[X]) (g : ℕ → (ZMod 2)[X]) (l : List ℕ) :
    (l.map g).prod % P = (l.map (fun k => g k % P)).prod % P := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [Polynomial.mul_mod, ih, ← Polynomial.mul_mod]
    rw [Polynomial.mul_mod (g a % P), modmod, Polynomial.mul_mod (g a)]

theorem foldl_mod (P : (ZMod 2)[X]) (f : ℕ → (ZMod 2)[X]) (l : List ℕ) :
    ∀ a : (ZMod 2)[X], l.foldl (fun a k => (a * f k) % P) (a % P) = (a * (l.map f).prod) % P := by
  induction l with
  | nil => intro a; simp
  | cons k l ih =>
    intro a
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [mulmod, ih, mul_assoc]

theorem pow_sum (l : List ℕ) :
    (X : (ZMod 2)[X]) ^ (l.map (fun i => 2 ^ i)).sum = (l.map fun k => (X : (ZMod 2)[X]) ^ (2 ^ k)).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [pow_add, ih]

theorem len_le (N : ℕ) : N.bitIndices.length ≤ Nat.log 2 N + 1 := by
  have hnd := Nat.bitIndices_nodup (n := N)
  have : N.bitIndices.toFinset ⊆ Finset.range (Nat.log 2 N + 1) := by
    intro i hi
    rw [List.mem_toFinset] at hi
    have hN : N ≠ 0 := by
      rintro rfl; simp at hi
    have h2 : 2 ^ i ≤ N := by
      calc 2 ^ i ≤ (N.bitIndices.map (fun i => 2 ^ i)).sum :=
            List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨i, hi, rfl⟩)
        _ = N := Nat.sum_map_two_pow_bitIndices N
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.le_log_of_pow_le (by norm_num) h2
  have := Finset.card_le_card this
  rwa [List.toFinset_card_of_nodup hnd, Finset.card_range] at this

end KadatchJenkinsS4a

theorem solution (P : (ZMod 2)[X]) (_hP : 0 < P.natDegree) (N : ℕ) :
    (X : (ZMod 2)[X]) ^ N = (N.bitIndices.map fun k => (X : (ZMod 2)[X]) ^ (2 ^ k)).prod ∧
      X ^ N % P = (N.bitIndices.map (KadatchJenkins.pow2k P)).prod % P ∧
      X ^ N % P = N.bitIndices.foldl (fun a k => (a * KadatchJenkins.pow2k P k) % P) (1 % P) ∧
      N.bitIndices.length ≤ Nat.log 2 N + 1 := by
  have h1 : (X : (ZMod 2)[X]) ^ N = (N.bitIndices.map fun k => (X : (ZMod 2)[X]) ^ (2 ^ k)).prod := by
    conv_lhs => rw [← Nat.sum_map_two_pow_bitIndices N]
    exact KadatchJenkinsS4a.pow_sum _
  have h2 : X ^ N % P = (N.bitIndices.map (KadatchJenkins.pow2k P)).prod % P := by
    rw [h1, KadatchJenkinsS4a.prod_mod]
    rfl
  refine ⟨h1, h2, ?_, KadatchJenkinsS4a.len_le N⟩
  rw [KadatchJenkinsS4a.foldl_mod P (KadatchJenkins.pow2k P) N.bitIndices 1, one_mul, h2]
