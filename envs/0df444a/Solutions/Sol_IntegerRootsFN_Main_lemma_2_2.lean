-- Prove2me | solution 1 for IntegerRootsFN.Main.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @fffmath
-- created : 2026-11-13T08:08:48.477204+00:00
-- url     : https://prove2.me/submissions/2235550a-1571-4960-99a4-dc4f1361386c

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_PolynomialData

set_option autoImplicit false

open Polynomial IntegerRootsFN.Main

-- The auxiliary statements below translate IntegerRootFinding/LeadingPart.lean.
private def coeffBitBound (f : Polynomial ℤ) (b : ℕ) : Prop :=
  ∀ i : ℕ, Int.natAbs (f.coeff i) < 2 ^ b

private noncomputable def leadingPart (f : Polynomial ℤ) (n d : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range (d + 1), Polynomial.monomial (d - j) (f.coeff (n - j))

/-- The leading part's coefficients are the original high coefficients shifted down to start at zero. -/
private theorem leadingPart_coeff (f : Polynomial ℤ) {n d : ℕ} (hd : d ≤ n) (k : ℕ) :
    (leadingPart f n d).coeff k = if k ≤ d then f.coeff (n - d + k) else 0 := by
  classical
  simp only [leadingPart, finsetSum_coeff, coeff_monomial]
  by_cases hk : k ≤ d
  · rw [if_pos hk, Finset.sum_eq_single (d - k)]
    · simp only [show d - (d - k) = k by omega, ite_true]
      congr 1
      omega
    · intro j hj hne
      have hj' := Finset.mem_range.mp hj
      have : d - j ≠ k := by omega
      simp [this]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro j hj
    have : d - j ≠ k := by omega
    simp [this]

/-- Keeping all coefficients of a polynomial recovers the original polynomial. -/
private theorem leadingPart_self (f : Polynomial ℤ) {n : ℕ} (hdeg : f.natDegree = n) :
    leadingPart f n n = f := by
  ext k
  rw [leadingPart_coeff f le_rfl]
  by_cases hk : k ≤ n
  · simp [hk]
  · rw [if_neg hk, coeff_eq_zero_of_natDegree_lt (by omega)]

/-- The low-degree tail consisting of coefficients below the cutoff. -/
private noncomputable def leadingPartTail (f : Polynomial ℤ) (k : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range k, monomial i (f.coeff i)

/-- The tail retains coefficients strictly below the cutoff and vanishes above it. -/
private theorem leadingPartTail_coeff (f : Polynomial ℤ) (k i : ℕ) :
    (leadingPartTail f k).coeff i = if i < k then f.coeff i else 0 := by
  classical
  simp only [leadingPartTail, finsetSum_coeff, coeff_monomial]
  by_cases hi : i < k
  · rw [if_pos hi, Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [hji]
    · simp [hi]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    have : j ≠ i := by have := Finset.mem_range.mp hj; omega
    simp [this]

/-- Decompose a polynomial into a power of the variable times its leading part plus the low-degree tail. -/
private theorem leadingPart_decomposition (f : Polynomial ℤ) {n d : ℕ}
    (hdeg : f.natDegree = n) (hd : d ≤ n) :
    f = X ^ (n - d) * leadingPart f n d + leadingPartTail f (n - d) := by
  ext k
  rw [coeff_add, coeff_X_pow_mul', leadingPart_coeff f hd, leadingPartTail_coeff]
  by_cases hk : n - d ≤ k
  · rw [if_pos hk, if_neg (by omega : ¬ k < n - d), add_zero]
    by_cases hkd : k - (n - d) ≤ d
    · rw [if_pos hkd]
      congr 1
      omega
    · rw [if_neg hkd, coeff_eq_zero_of_natDegree_lt (by omega)]
  · simp [hk, show k < n - d by omega]

/-- Truncating a nonzero degree-`n` polynomial to its leading `d+1` coefficients gives degree `d`. -/
private theorem leadingPart_natDegree (f : Polynomial ℤ) {n d : ℕ}
    (hdeg : f.natDegree = n) (hd : d ≤ n) (hf : f ≠ 0) :
    (leadingPart f n d).natDegree = d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [leadingPart_coeff f hd, if_neg (by omega)]
  · rw [leadingPart_coeff f hd, if_pos le_rfl, Nat.sub_add_cancel hd, ← hdeg]
    simpa only [coeff_natDegree] using (leadingCoeff_ne_zero.mpr hf)

private theorem leadingPart_geom_sum_lt {R : ℝ} (hR : 2 ≤ R) (k : ℕ) :
    (∑ i ∈ Finset.range k, R ^ i) < R ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hp : 0 ≤ R ^ k := pow_nonneg (by linarith) _
    calc
      (∑ i ∈ Finset.range k, R ^ i) + R ^ k < R ^ k + R ^ k :=
        by linarith
      _ = R ^ k * 2 := by ring
      _ ≤ R ^ k * R := mul_le_mul_of_nonneg_left hR hp

/-- Bound the low-degree tail at points of modulus at least two by the coefficient scale. -/
private theorem leadingPartTail_eval_lt (f : Polynomial ℤ) (b k : ℕ)
    (hcoeff : coeffBitBound f b) (z : ℂ) (hz : 2 ≤ ‖z‖) :
    ‖(complexify (leadingPartTail f k)).eval z‖ < (2 : ℝ) ^ b * ‖z‖ ^ k := by
  classical
  have hc (i : ℕ) : ‖(f.coeff i : ℂ)‖ ≤ (2 : ℝ) ^ b := by
    rw [← norm_natAbs, Complex.norm_natCast]
    exact_mod_cast (hcoeff i).le
  have he : (complexify (leadingPartTail f k)).eval z =
      ∑ i ∈ Finset.range k, (f.coeff i : ℂ) * z ^ i := by
    simp [complexify, leadingPartTail, Polynomial.map_sum, eval_finsetSum]
  rw [he]
  calc
    ‖∑ i ∈ Finset.range k, (f.coeff i : ℂ) * z ^ i‖
        ≤ ∑ i ∈ Finset.range k, ‖(f.coeff i : ℂ) * z ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range k, (2 : ℝ) ^ b * ‖z‖ ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right (hc i) (by positivity)
    _ = (2 : ℝ) ^ b * ∑ i ∈ Finset.range k, ‖z‖ ^ i := by rw [Finset.mul_sum]
    _ < (2 : ℝ) ^ b * ‖z‖ ^ k :=
      mul_lt_mul_of_pos_left (leadingPart_geom_sum_lt hz k) (by positivity)

/-- At a large integer root, the leading part's evaluation is smaller than the coefficient scale. -/
private theorem leadingPart_eval_lt (f : Polynomial ℤ) {n d b : ℕ}
    (hdeg : f.natDegree = n) (hd : d ≤ n) (hcoeff : coeffBitBound f b)
    (r : ℤ) (hr : f.eval r = 0) (hrabs : 2 ≤ r.natAbs) :
    ‖(complexify (leadingPart f n d)).eval (r : ℂ)‖ < (2 : ℝ) ^ b := by
  have hrnorm : 2 ≤ ‖(r : ℂ)‖ := by
    rw [← norm_natAbs, Complex.norm_natCast]
    exact_mod_cast hrabs
  have he : (r : ℂ) ^ (n - d) *
      (complexify (leadingPart f n d)).eval (r : ℂ) +
      (complexify (leadingPartTail f (n - d))).eval (r : ℂ) = 0 := by
    have heq := congrArg (fun p : Polynomial ℤ =>
      (complexify p).eval (r : ℂ)) (leadingPart_decomposition f hdeg hd)
    simpa [complexify, hr] using heq.symm
  have hn : ‖(r : ℂ)‖ ^ (n - d) *
      ‖(complexify (leadingPart f n d)).eval (r : ℂ)‖ =
      ‖(complexify (leadingPartTail f (n - d))).eval (r : ℂ)‖ := by
    have := congrArg norm (eq_neg_of_add_eq_zero_left he)
    simpa only [norm_mul, norm_pow, norm_neg] using this
  have hb := leadingPartTail_eval_lt f b (n - d) hcoeff (r : ℂ) hrnorm
  rw [← hn, mul_comm ((2 : ℝ) ^ b)] at hb
  exact (mul_lt_mul_iff_right₀ (pow_pos (by linarith : 0 < ‖(r : ℂ)‖) _)).mp hb

private theorem leadingPart_two_pow_card_le (s : Multiset ℂ)
    (hs : ∀ z ∈ s, 2 ≤ ‖z‖) : (2 : ℝ) ^ s.card ≤ ‖s.prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.card_cons, Multiset.prod_cons, norm_mul, pow_succ]
    have ha : 2 ≤ ‖a‖ := hs a (Multiset.mem_cons_self _ _)
    have ht : (2 : ℝ) ^ s.card ≤ ‖s.prod‖ :=
      ih (fun z hz => hs z (Multiset.mem_cons_of_mem hz))
    calc
      (2 : ℝ) ^ s.card * 2 ≤ ‖s.prod‖ * 2 :=
        mul_le_mul_of_nonneg_right ht (by norm_num)
      _ = 2 * ‖s.prod‖ := mul_comm _ _
      _ ≤ ‖a‖ * ‖s.prod‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)

/-- A nonzero integer polynomial with sufficiently small evaluation has a root within distance two. -/
private theorem leadingPart_exists_root_near (g : Polynomial ℤ) (z : ℂ) (hg : g ≠ 0)
    (hsmall : ‖(complexify g).eval z‖ < (2 : ℝ) ^ g.natDegree) :
    ∃ α : ℂ, (complexify g).eval α = 0 ∧ ‖z - α‖ < 2 := by
  classical
  let p := complexify g
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hp : p ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff hinj).mpr hg
  have hdegree : p.natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj g
  have hlc : 1 ≤ ‖p.leadingCoeff‖ := by
    have hne : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg
    have hn : 1 ≤ g.leadingCoeff.natAbs := by
      have := Int.natAbs_pos.mpr hne
      omega
    change 1 ≤ ‖(g.map (Int.castRingHom ℂ)).leadingCoeff‖
    rw [leadingCoeff_map_of_injective hinj]
    change 1 ≤ ‖(g.leadingCoeff : ℂ)‖
    rw [← norm_natAbs, Complex.norm_natCast]
    exact_mod_cast hn
  by_contra h
  have hfar : ∀ α ∈ p.roots, 2 ≤ ‖z - α‖ := by
    intro α hα
    have hroot : p.eval α = 0 := (mem_roots hp).mp hα
    exact le_of_not_gt (fun hlt => h ⟨α, hroot, hlt⟩)
  have hprod : (2 : ℝ) ^ p.roots.card ≤ ‖(p.roots.map (z - ·)).prod‖ := by
    have := leadingPart_two_pow_card_le (p.roots.map (z - ·)) (by
      intro a ha
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp ha
      exact hfar α hα)
    simpa using this
  have hsplit := IsAlgClosed.splits p
  have he := hsplit.eval_eq_prod_roots z
  have hlower : (2 : ℝ) ^ g.natDegree ≤ ‖p.eval z‖ := by
    rw [he, norm_mul]
    have hcard : p.roots.card = g.natDegree := by
      rw [← hsplit.natDegree_eq_card_roots, hdegree]
    rw [hcard] at hprod
    calc
      (2 : ℝ) ^ g.natDegree ≤ ‖(p.roots.map (z - ·)).prod‖ := hprod
      _ = 1 * ‖(p.roots.map (z - ·)).prod‖ := (one_mul _).symm
      _ ≤ ‖p.leadingCoeff‖ * ‖(p.roots.map (z - ·)).prod‖ :=
        mul_le_mul_of_nonneg_right hlc (norm_nonneg _)
  exact (not_lt_of_ge hlower) hsmall

/-- Reindexing the source leading part gives the platform truncation. -/
private theorem leadingPart_eq_truncate (f : Polynomial ℤ) (n b : ℕ) :
    leadingPart f n (min n b) = truncate f n b := by
  classical
  ext k
  rw [leadingPart_coeff f (Nat.min_le_left n b)]
  simp only [truncate, finsetSum_coeff, coeff_monomial]
  by_cases hk : k ≤ min n b
  · rw [if_pos hk, Finset.sum_eq_single k]
    · simp
    · intro j hj hji
      simp [hji]
    · simp [Finset.mem_range, hk]
  · rw [if_neg hk]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j ≠ k := by
      have := Finset.mem_range.mp hj
      omega
    simp [hji]

theorem solution (n b : ℕ) (f : Polynomial ℤ) (hf : Valid f n b)
    (hd : min n b < n) (r : ℤ) (hr : f.IsRoot r) (hrlarge : 2 ≤ |r|) :
    ∃ α : ℂ, (complexify (truncate f n b)).IsRoot α ∧ ‖(r : ℂ) - α‖ < 2 := by
  have hdeg : f.natDegree = n := hf.2.2.1
  have hcoeff : coeffBitBound f b := by
    intro i
    have hi : ((f.coeff i).natAbs : ℤ) < (2 : ℤ) ^ b := by
      simpa only [Int.natCast_natAbs] using hf.2.2.2.2 i
    exact_mod_cast hi
  have hrabs : 2 ≤ r.natAbs := by
    have h : (2 : ℤ) ≤ (r.natAbs : ℤ) := by
      simpa only [Int.natCast_natAbs] using hrlarge
    exact_mod_cast h
  have hdn : min n b ≤ n := Nat.min_le_left _ _
  have hdb : min n b = b := by omega
  have hfne : f ≠ 0 := by
    intro hzero
    exact hf.2.2.2.1 (by simp [hzero])
  have hg : (leadingPart f n (min n b)).natDegree = min n b :=
    leadingPart_natDegree f hdeg hdn hfne
  have hgne : leadingPart f n (min n b) ≠ 0 := by
    intro hzero
    have hlead := leadingPart_coeff f hdn (min n b)
    rw [hzero, Polynomial.coeff_zero, if_pos le_rfl,
      Nat.sub_add_cancel hdn] at hlead
    exact hf.2.2.2.1 hlead.symm
  rw [← leadingPart_eq_truncate f n b]
  apply leadingPart_exists_root_near _ (r : ℂ) hgne
  rw [hg, hdb]
  simpa only [hdb] using leadingPart_eval_lt f hdeg hdn hcoeff r hr hrabs
