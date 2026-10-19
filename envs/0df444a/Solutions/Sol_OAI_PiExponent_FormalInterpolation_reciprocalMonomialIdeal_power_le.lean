-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.reciprocalMonomialIdeal_power_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:58:04.144044+00:00
-- url     : https://prove2.me/submissions/d7be7cf5-9a79-422b-ac70-1da44822b618

import Mathlib
import Definitions.Def_OAI_PiExponent_ReciprocalMonomialIdeal

open OAI.PiExponent.FormalInterpolation


theorem solution
    {R : Type*} [CommRing R] {m : Nat}
    (x : Fin (m + 1) → R) (e : Fin (m + 1) → Nat)
    (he : ∀ i, 0 < e i) (n : Nat) :
    (reciprocalMonomialIdeal x e 1) ^ (n + m) ≤
      (Ideal.span (Set.range (fun i => x i ^ e i))) ^ n := by
  classical
  have hmul : ∀ D1 D2 : ℚ, reciprocalMonomialIdeal x e D1 * reciprocalMonomialIdeal x e D2 ≤
      reciprocalMonomialIdeal x e (D1 + D2) := by
    intro D1 D2
    unfold reciprocalMonomialIdeal
    rw [Ideal.span_mul_span']
    apply Ideal.span_mono
    rintro r ⟨r1, ⟨a, ha, rfl⟩, r2, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨a + b, ?_, ?_⟩
    · simp only [Pi.add_apply, Nat.cast_add, add_div, Finset.sum_add_distrib]; linarith
    · simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  have hpow : ∀ k : ℕ, reciprocalMonomialIdeal x e 1 ^ k ≤ reciprocalMonomialIdeal x e k := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
      apply Ideal.subset_span
      exact ⟨0, by simp, by simp⟩
    | succ k ih =>
      rw [pow_succ]
      calc reciprocalMonomialIdeal x e 1 ^ k * reciprocalMonomialIdeal x e 1
          ≤ reciprocalMonomialIdeal x e k * reciprocalMonomialIdeal x e 1 := Ideal.mul_mono_left ih
        _ ≤ reciprocalMonomialIdeal x e ((k : ℚ) + 1) := hmul _ _
        _ = reciprocalMonomialIdeal x e ((k + 1 : ℕ) : ℚ) := by push_cast; rfl
  refine (hpow (n + m)).trans ?_
  unfold reciprocalMonomialIdeal
  rw [Ideal.span_le]
  rintro r ⟨a, ha, rfl⟩
  set J := Ideal.span (Set.range (fun i => x i ^ e i))
  set q : Fin (m + 1) → ℕ := fun i => a i / e i
  have hsplit : ∏ i, x i ^ a i = (∏ i, (x i ^ e i) ^ q i) * ∏ i, x i ^ (a i % e i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← pow_mul, ← pow_add]; congr 1; simp only [q]; exact (Nat.div_add_mod (a i) (e i)).symm
  have hq : n ≤ ∑ i, q i := by
    have hlt : ∀ i, (a i : ℚ) / e i < q i + 1 := by
      intro i
      have hei : (0:ℚ) < e i := by exact_mod_cast he i
      rw [div_lt_iff₀ hei]
      have : a i < (q i + 1) * e i := by
        simp only [q]
        have := Nat.lt_div_mul_add (a := a i) (he i)
        nlinarith [Nat.div_add_mod (a i) (e i), Nat.mod_lt (a i) (he i)]
      exact_mod_cast this
    have hsum : (∑ i, (a i : ℚ) / e i) < ∑ i, ((q i : ℚ) + 1) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hlt i)
    rw [Finset.sum_add_distrib] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
    push_cast at ha hsum
    have : (n : ℚ) < (∑ i, (q i : ℚ)) + 1 := by linarith
    have : n < (∑ i, q i) + 1 := by exact_mod_cast this
    omega
  rw [hsplit]
  apply Ideal.mul_mem_right
  apply Ideal.pow_le_pow_right hq
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Ideal.prod_mem_prod
  intro i _
  exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

