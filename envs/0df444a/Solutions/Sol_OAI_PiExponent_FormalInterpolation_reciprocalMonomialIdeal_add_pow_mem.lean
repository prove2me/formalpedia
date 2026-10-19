-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.reciprocalMonomialIdeal_add_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:57:02.112489+00:00
-- url     : https://prove2.me/submissions/04e64b81-5511-45a0-8e0a-f3864102989c

import Mathlib
import Definitions.Def_OAI_PiExponent_ReciprocalMonomialIdeal

open OAI.PiExponent.FormalInterpolation


theorem solution
    {R : Type*} [CommRing R] {d : Nat}
    (x : Fin d → R) (e : Fin d → Nat) (he : ∀ k, 0 < e k)
    (i j : Fin d) (t : Nat) (ht : e j ≤ t * e i) (a : R) :
    (x i + x j ^ t * a) ^ e i ∈ reciprocalMonomialIdeal x e 1 := by
  classical
  rw [add_pow]
  apply Ideal.sum_mem
  intro k hk
  have hk' : k ≤ e i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  set s := t * (e i - k)
  have hmono : x i ^ k * x j ^ s ∈ reciprocalMonomialIdeal x e 1 := by
    apply Ideal.subset_span
    refine ⟨Pi.single i k + Pi.single j s, ?_, ?_⟩
    · simp only [Pi.add_apply, Nat.cast_add, add_div, Finset.sum_add_distrib]
      have h1 : ∑ l, ((Pi.single i k : Fin d → ℕ) l : ℚ) / (e l : ℚ) = (k : ℚ) / e i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro l _ hl; simp [Pi.single_apply, hl]
        · simp
      have h2 : ∑ l, ((Pi.single j s : Fin d → ℕ) l : ℚ) / (e l : ℚ) = (s : ℚ) / e j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro l _ hl; simp [Pi.single_apply, hl]
        · simp
      rw [h1, h2]
      have hei : (0:ℚ) < e i := by exact_mod_cast he i
      have hej : (0:ℚ) < e j := by exact_mod_cast he j
      have hs : (s : ℚ) = t * ((e i : ℚ) - k) := by
        simp only [s]; push_cast [Nat.cast_sub hk']; ring
      have ht' : (e j : ℚ) ≤ t * e i := by exact_mod_cast ht
      have h3 : ((e i : ℚ) - k) / e i ≤ (s : ℚ) / e j := by
        rw [div_le_div_iff₀ hei hej, hs]
        have : (0:ℚ) ≤ (e i : ℚ) - k := by
          have : (k:ℚ) ≤ e i := by exact_mod_cast hk'
          linarith
        nlinarith
      have h4 : (k : ℚ) / e i + ((e i : ℚ) - k) / e i = 1 := by
        field_simp; ring
      linarith
    · simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, Pi.single_apply, pow_ite, pow_zero,
        Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have e1 : x i ^ k * (x j ^ t * a) ^ (e i - k) * ((e i).choose k : R) =
      (x i ^ k * x j ^ s) * (a ^ (e i - k) * ((e i).choose k : R)) := by
    simp only [s, mul_pow, pow_mul]; ring
  rw [e1]
  exact Ideal.mul_mem_right _ _ hmono

