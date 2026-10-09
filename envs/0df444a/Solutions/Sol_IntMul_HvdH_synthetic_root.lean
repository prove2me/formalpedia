-- Prove2me | solution 1 for IntMul.HvdH.synthetic_root
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T10:00:23.517997+00:00
-- url     : https://prove2.me/submissions/9a012cfc-0f83-4e1c-962f-14a96be80ffe

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

open Polynomial
open scoped BigOperators

private lemma root_pow_neg_one (r : ℕ) :
    AdjoinRoot.root (X ^ r + C (1 : ℂ)) ^ r = -1 := by
  have h := AdjoinRoot.eval₂_root (X ^ r + C (1 : ℂ))
  rw [eval₂_add, eval₂_pow, eval₂_X, eval₂_C, map_one] at h
  exact eq_neg_of_add_eq_zero_left h

-- A half-period equal to -1 makes the difference from 1 a unit.
private lemma unit_sub_one {R : Type*} [CommRing R] [Algebra ℂ R]
    (x : R) (q : ℕ) (hx : x ^ q = -1) : IsUnit (x - 1) := by
  have h2 : IsUnit (-2 : R) := by
    have hc : IsUnit (-2 : ℂ) := isUnit_iff_ne_zero.mpr (by norm_num)
    simpa only [map_neg, map_ofNat] using IsUnit.map (algebraMap ℂ R) hc
  have hm : (∑ i ∈ Finset.range q, x ^ i) * (x - 1) = (-2 : R) := by
    rw [geom_sum_mul, hx]
    ring
  have hu : IsUnit ((∑ i ∈ Finset.range q, x ^ i) * (x - 1)) := by
    rw [hm]
    exact h2
  exact isUnit_of_mul_isUnit_right hu

-- Powers of a root whose half-order is a power of two avoid 1 by a unit.
private lemma unit_pow_sub_one {R : Type*} [CommRing R] [Algebra ℂ R]
    (s : ℕ) (y : R) (hy : y ^ (2 ^ s) = -1) (j : ℕ)
    (hj : ¬ 2 ^ (s + 1) ∣ j) : IsUnit (y ^ j - 1) := by
  induction s generalizing y j with
  | zero =>
    have ho : Odd j := by
      rcases Nat.even_or_odd j with he | ho
      · exfalso
        apply hj
        simpa using even_iff_two_dvd.mp he
      · exact ho
    apply unit_sub_one (y ^ j) (2 ^ 0)
    rw [pow_right_comm, hy, ho.neg_one_pow]
  | succ s ih =>
    rcases Nat.even_or_odd j with he | ho
    · obtain ⟨t, ht⟩ := he
      have hje : j = 2 * t := by omega
      have hy2 : (y ^ 2) ^ (2 ^ s) = -1 := by
        rw [← pow_mul]
        simpa [pow_succ, mul_comm] using hy
      have ht' : ¬ 2 ^ (s + 1) ∣ t := by
        intro hd
        apply hj
        rw [hje, pow_succ]
        simpa [mul_comm] using Nat.mul_dvd_mul_left 2 hd
      have hu := ih (y ^ 2) hy2 t ht'
      simpa [← pow_mul, hje] using hu
    · apply unit_sub_one (y ^ j) (2 ^ (s + 1))
      rw [pow_right_comm, hy, ho.neg_one_pow]

private lemma synthetic_period (r n : ℕ) (hdiv : n ∣ 2 * r) :
    (AdjoinRoot.root (X ^ r + C (1 : ℂ)) ^ (2 * r / n)) ^ n = 1 := by
  rw [← pow_mul, Nat.div_mul_cancel hdiv, mul_comm 2 r, pow_mul, root_pow_neg_one]
  norm_num

private lemma synthetic_sum (r : ℕ) (hr : 0 < r) (hpow : ∃ s : ℕ, r = 2 ^ s)
    (n : ℕ) (hn : 0 < n) (hdiv : n ∣ 2 * r) (j : ℕ) (hj : ¬ n ∣ j) :
    ∑ k ∈ Finset.range n,
      ((AdjoinRoot.root (X ^ r + C (1 : ℂ)) ^ (2 * r / n)) ^ j) ^ k = 0 := by
  let y := AdjoinRoot.root (X ^ r + C (1 : ℂ))
  let a := 2 * r / n
  have ha : 0 < a := Nat.div_pos (Nat.le_of_dvd (by positivity) hdiv) hn
  have han : a * n = 2 * r := Nat.div_mul_cancel hdiv
  have hnj : ¬ 2 * r ∣ a * j := by
    intro hd
    apply hj
    rw [← han] at hd
    exact (Nat.mul_dvd_mul_iff_left ha).mp hd
  obtain ⟨s, hs⟩ := hpow
  have hu : IsUnit ((y ^ a) ^ j - 1) := by
    rw [← pow_mul]
    apply unit_pow_sub_one s y
    · simpa [hs, y] using root_pow_neg_one r
    · simpa [pow_succ, hs, mul_comm] using hnj
  apply hu.mul_left_eq_zero.mp
  rw [geom_sum_mul, pow_right_comm, synthetic_period r n hdiv, one_pow, sub_self]

private lemma representative_degree (r : ℕ) (hr : 0 < r)
    (hmon : (X ^ r + C (1 : ℂ)).Monic)
    (u : AdjoinRoot (X ^ r + C (1 : ℂ))) :
    (AdjoinRoot.modByMonicHom hmon u).degree < r := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective u
  rw [AdjoinRoot.modByMonicHom_mk]
  simpa only [degree_X_pow_add_C hr] using degree_modByMonic_lt p hmon

-- Multiplication by y is a signed cyclic shift of the canonical coefficients.
private lemma root_mul_coeff (r : ℕ) (hr : 0 < r)
    (hmon : (X ^ r + C (1 : ℂ)).Monic)
    (u : AdjoinRoot (X ^ r + C (1 : ℂ))) :
    (AdjoinRoot.modByMonicHom hmon (AdjoinRoot.root _ * u)).coeff 0 =
      -(AdjoinRoot.modByMonicHom hmon u).coeff (r - 1) ∧
    ∀ i : ℕ, i + 1 < r →
      (AdjoinRoot.modByMonicHom hmon (AdjoinRoot.root _ * u)).coeff (i + 1) =
        (AdjoinRoot.modByMonicHom hmon u).coeff i := by
  let f : ℂ[X] := X ^ r + C (1 : ℂ)
  let p : ℂ[X] := AdjoinRoot.modByMonicHom hmon u
  let q : ℂ[X] := X * p - C (p.coeff (r - 1)) * f
  have hp : p.degree < r := representative_degree r hr hmon u
  have hq0 : q.coeff 0 = -p.coeff (r - 1) := by
    simp [q, f, hr.ne]
  have hqs (i : ℕ) : q.coeff (i + 1) =
      p.coeff i - if i + 1 = r then p.coeff (r - 1) else 0 := by
    simp only [q, f, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_add, coeff_X_pow,
      coeff_C, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, add_zero]
    split_ifs <;> simp_all
  have hqdeg : q.degree < r := by
    apply (degree_lt_iff_coeff_zero q r).mpr
    intro m hm
    cases m with
    | zero => omega
    | succ i =>
      rw [hqs]
      by_cases hi : i + 1 = r
      · rw [if_pos hi]
        have hir : i = r - 1 := by omega
        rw [hir, sub_self]
      · rw [if_neg hi, sub_zero]
        exact (degree_lt_iff_coeff_zero p r).mp hp i (by omega)
  have hmk : AdjoinRoot.mk f q = AdjoinRoot.root f * u := by
    dsimp only [q]
    simp only [map_sub, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_self, mul_zero, sub_zero]
    rw [AdjoinRoot.mk_leftInverse hmon u]
  have hrepr : AdjoinRoot.modByMonicHom hmon (AdjoinRoot.root f * u) = q := by
    rw [← hmk, AdjoinRoot.modByMonicHom_mk]
    apply (modByMonic_eq_self_iff hmon).mpr
    simpa only [f, degree_X_pow_add_C hr] using hqdeg
  rw [hrepr]
  constructor
  · exact hq0
  · intro i hi
    rw [hqs, if_neg (by omega), sub_zero]

private lemma root_mul_bounds (r : ℕ) (hr : 0 < r)
    (hmon : (X ^ r + C (1 : ℂ)).Monic)
    (u : AdjoinRoot (X ^ r + C (1 : ℂ))) (B : ℝ) :
    (∀ i < r, ‖(AdjoinRoot.modByMonicHom hmon (AdjoinRoot.root _ * u)).coeff i‖ ≤ B) ↔
      (∀ i < r, ‖(AdjoinRoot.modByMonicHom hmon u).coeff i‖ ≤ B) := by
  obtain ⟨hc0, hcs⟩ := root_mul_coeff r hr hmon u
  constructor
  · intro h i hi
    by_cases hilast : i + 1 = r
    · have hb := h 0 hr
      rw [hc0, norm_neg] at hb
      have hir : r - 1 = i := by omega
      simpa only [hir] using hb
    · have hb := h (i + 1) (by omega)
      rw [hcs i (by omega)] at hb
      exact hb
  · intro h i hi
    cases i with
    | zero =>
      rw [hc0, norm_neg]
      exact h (r - 1) (by omega)
    | succ i =>
      rw [hcs i hi]
      exact h i (by omega)

private lemma root_pow_bounds (r : ℕ) (hr : 0 < r)
    (hmon : (X ^ r + C (1 : ℂ)).Monic) (a : ℕ)
    (u : AdjoinRoot (X ^ r + C (1 : ℂ))) (B : ℝ) :
    (∀ i < r, ‖(AdjoinRoot.modByMonicHom hmon (AdjoinRoot.root _ ^ a * u)).coeff i‖ ≤ B) ↔
      (∀ i < r, ‖(AdjoinRoot.modByMonicHom hmon u).coeff i‖ ≤ B) := by
  induction a with
  | zero => simp
  | succ a ih =>
    calc
      (∀ i < r, ‖(AdjoinRoot.modByMonicHom hmon
          (AdjoinRoot.root _ ^ (a + 1) * u)).coeff i‖ ≤ B) ↔
          (∀ i < r, ‖(AdjoinRoot.modByMonicHom hmon (AdjoinRoot.root _ ^ a * u)).coeff i‖ ≤ B) := by
        rw [pow_succ', mul_assoc]
        exact
          root_mul_bounds r hr hmon (AdjoinRoot.root _ ^ a * u) B
      _ ↔ _ := ih

-- Exact type of IntMul.HvdH.synthetic_root; all auxiliary results are proved.
theorem solution (r : ℕ) (hr : 2 ≤ r) (hpow : ∃ k : ℕ, r = 2 ^ k) (n : ℕ) (hn : 0 < n)
    (hdiv : n ∣ 2 * r) :
    let hmon : (X ^ r + C (1 : ℂ)).Monic := monic_X_pow_add_C 1 (by omega)
    let ω : AdjoinRoot (X ^ r + C (1 : ℂ)) := AdjoinRoot.root _ ^ (2 * r / n)
    let c : AdjoinRoot (X ^ r + C (1 : ℂ)) → ℕ → ℂ := fun u i =>
      (AdjoinRoot.modByMonicHom hmon u).coeff i
    ω ^ n = 1 ∧
      (∀ j : ℕ, ¬ n ∣ j → ∑ k ∈ Finset.range n, (ω ^ j) ^ k = 0) ∧
      (∀ (u : AdjoinRoot (X ^ r + C (1 : ℂ))) (B : ℝ),
        (∀ i < r, ‖c (ω * u) i‖ ≤ B) ↔ (∀ i < r, ‖c u i‖ ≤ B)) := by
  dsimp only
  refine ⟨synthetic_period r n hdiv, ?_, ?_⟩
  · intro j hj
    exact synthetic_sum r (by omega) hpow n hn hdiv j hj
  · intro u B
    exact root_pow_bounds r (by omega) (monic_X_pow_add_C 1 (by omega)) (2 * r / n) u B
