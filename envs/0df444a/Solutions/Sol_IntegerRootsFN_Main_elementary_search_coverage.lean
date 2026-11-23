-- Prove2me | solution 1 for IntegerRootsFN.Main.elementary_search_coverage
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:51:18.597583+00:00
-- url     : https://prove2.me/submissions/35330dcf-588b-4f33-83fb-79344a99c407
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ElementarySearch
import Theorems.Thm_IntegerRootsFN_Main_lemma_A_2
import Theorems.Thm_IntegerRootsFN_Main_lemma_2_2

set_option autoImplicit false

open Polynomial IntegerRootsFN.Main

private lemma trunc_coeff (f : Polynomial ℤ) (n b k : ℕ) :
    (truncate f n b).coeff k =
      if k ≤ min n b then f.coeff (n - min n b + k) else 0 := by
  classical
  simp only [truncate, finsetSum_coeff, coeff_monomial]
  by_cases hk : k ≤ min n b
  · rw [if_pos hk, Finset.sum_eq_single k]
    · simp
    · intro j hj hji
      simp only [Finset.mem_range] at hj
      have : j ≠ k := by omega
      simp [this]
    · simp [Finset.mem_range, hk]
  · rw [if_neg hk]
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hji : j ≠ k := by
      have := Finset.mem_range.mp hj
      omega
    simp [hji]

private lemma trunc_eq_of_min_eq (f : Polynomial ℤ) (n b : ℕ)
    (hn : min n b = n) (hdeg : f.natDegree = n) : truncate f n b = f := by
  ext k
  rw [trunc_coeff, hn]
  by_cases hk : k ≤ n
  · simp [hk]
  · rw [if_neg hk]
    symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega

private lemma geom_sum_bound {R B : ℝ} (hR : 2 ≤ R) (hB : B + 1 ≤ R) (n : ℕ) :
    B * ∑ i ∈ Finset.range n, R ^ i < R ^ n := by
  have hR0 : 0 < R := by linarith
  have hgeom : (R - 1) * ∑ i ∈ Finset.range n, R ^ i = R ^ n - 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      rw [mul_add, ih]
      ring
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range n, R ^ i :=
    Finset.sum_nonneg (fun _ _ => pow_nonneg hR0.le _)
  have hmul : B * ∑ i ∈ Finset.range n, R ^ i ≤
      (R - 1) * ∑ i ∈ Finset.range n, R ^ i := by nlinarith
  rw [hgeom] at hmul
  have hn : 1 ≤ R ^ n := one_le_pow₀ (by linarith)
  linarith

private lemma integer_root_abs_le (f : Polynomial ℤ) (n b : ℕ) (hf : Valid f n b)
    (r : ℤ) (hr : f.IsRoot r) : |r| ≤ (2 : ℤ) ^ b := by
  by_contra hlarge
  have hn : 1 ≤ n := hf.1
  have hdeg : f.natDegree = n := hf.2.2.1
  let R : ℝ := |(r : ℝ)|
  have hRstep : ((2 : ℝ) ^ b) + 1 ≤ R := by
    have hi : ((2 : ℤ) ^ b) + 1 ≤ |r| := by omega
    have hir : (((2 : ℤ) ^ b + 1 : ℤ) : ℝ) ≤ |(r : ℝ)| := by exact_mod_cast hi
    norm_num [R] at hir ⊢
    exact hir
  have hRz : ((2 : ℝ) ^ b) < R := by linarith
  have hR : 2 ≤ R := by
    have hbp : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ b := pow_le_pow_right₀ (by norm_num) hf.2.1
    norm_num at hbp
    linarith
  have hev : (f.coeff n : ℂ) * (r : ℂ) ^ n +
      ∑ i ∈ Finset.range n, (f.coeff i : ℂ) * (r : ℂ) ^ i = 0 := by
    change f.eval r = 0 at hr
    rw [Polynomial.eval_eq_sum_range' (by omega : f.natDegree < n + 1)] at hr
    rw [Finset.sum_range_succ, add_comm] at hr
    exact_mod_cast hr
  have htail : ‖∑ i ∈ Finset.range n, (f.coeff i : ℂ) * (r : ℂ) ^ i‖ <
      R ^ n := by
    have hnorm_r : ‖(r : ℂ)‖ = R := by simp [R]
    calc
      _ ≤ ∑ i ∈ Finset.range n, ‖(f.coeff i : ℂ) * (r : ℂ) ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range n, (2 : ℝ) ^ b * R ^ _i := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, norm_pow, hnorm_r]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by dsimp [R]; positivity) _)
        have hc := hf.2.2.2.2 i
        have hc' : |(f.coeff i : ℝ)| ≤ (2 : ℝ) ^ b := by exact_mod_cast hc.le
        simpa using hc'
      _ = (2 : ℝ) ^ b * ∑ i ∈ Finset.range n, R ^ i := by rw [Finset.mul_sum]
      _ < R ^ n := geom_sum_bound (n := n) hR hRstep
  have hlead : 1 ≤ ‖(f.coeff n : ℂ)‖ := by
    rw [← norm_natAbs, Complex.norm_natCast]
    have : 1 ≤ (f.coeff n).natAbs := by
      have := Int.natAbs_pos.mpr hf.2.2.2.1
      omega
    exact_mod_cast this
  have hmain : R ^ n ≤ ‖(f.coeff n : ℂ) * (r : ℂ) ^ n‖ := by
    rw [norm_mul, norm_pow]
    have hnr : ‖(r : ℂ)‖ = R := by simp [R]
    rw [hnr]
    nlinarith [pow_nonneg (by dsimp [R]; positivity : 0 ≤ R) n]
  have heq : ‖(f.coeff n : ℂ) * (r : ℂ) ^ n‖ =
      ‖∑ i ∈ Finset.range n, (f.coeff i : ℂ) * (r : ℂ) ^ i‖ := by
    rw [← neg_eq_of_add_eq_zero_left hev, norm_neg]
  linarith

private lemma coverage_aux (n b : ℕ) (f : Polynomial ℤ) (hf : Valid f n b)
    (r : ℤ) (α : ℂ) (hα : (complexify (truncate f n b)).IsRoot α)
    (hnear : ‖(r : ℂ) - α‖ < 2) :
    ∀ (fuel : ℕ) (cs : List ℤ),
      (∃ m ∈ cs, |(r - m : ℤ)| ≤ (2 : ℤ) ^ fuel) →
      r ∈ searchScales (truncate f n b) (min n b) fuel (2 ^ fuel) cs := by
  intro fuel
  induction fuel with
  | zero =>
    intro cs hex
    obtain ⟨m, hm, hrm⟩ := hex
    have hnot : testEmpty (truncate f n b) (min n b) m (((2 ^ 0 : ℕ) : ℤ) + 2) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have hx := ((IntegerRootsFN.Main.lemma_A_2).1 n b f hf m (((2 ^ 0 : ℕ) : ℤ) + 2)
        (by simp)).1 ht α hα
      have htri : ‖α - (m : ℂ)‖ ≤ ‖α - (r : ℂ)‖ + ‖(r : ℂ) - (m : ℂ)‖ := by
        convert norm_add_le (α - (r : ℂ)) ((r : ℂ) - (m : ℂ)) using 1 <;> abel
      have hnr : ‖α - (r : ℂ)‖ < 2 := by simpa [norm_sub_rev] using hnear
      have hdist : ‖(r : ℂ) - (m : ℂ)‖ ≤ 1 := by
        have hir : |(r - m : ℤ)| ≤ (1 : ℤ) := by simpa using hrm
        have hreal : |(r - m : ℤ)| = ‖((r - m : ℤ) : ℂ)‖ := by
          rw [Complex.norm_intCast, Int.cast_abs]
        calc
          ‖(r : ℂ) - (m : ℂ)‖ = ‖((r - m : ℤ) : ℂ)‖ := by rw [Int.cast_sub]
          _ = |(r - m : ℤ)| := hreal.symm
          _ ≤ 1 := by exact_mod_cast hir
      norm_num at hx
      linarith
    norm_num [Nat.cast_pow] at hnot
    have hmkept : m ∈ cs.filter (fun m =>
        !(testEmpty (truncate f n b) (min n b) m (((2 ^ 0 : ℕ) : ℤ) + 2))) := by
      simp [List.mem_filter, hm, hnot]
    simp only [searchScales]
    rw [List.mem_eraseDups]
    simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨m, hmkept, ?_⟩
    simp only [pow_zero, Nat.cast_one] at hrm hmkept ⊢
    have hboth := abs_le.mp hrm
    omega
  | succ fuel ih =>
    intro cs hex
    obtain ⟨m, hm, hrm⟩ := hex
    have hpow : (2 : ℤ) ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
    have hnpow : (2 : ℕ) ^ (fuel + 1) / 2 = 2 ^ fuel := by
      rw [pow_succ, Nat.mul_div_left]
      norm_num
    have hnot : testEmpty (truncate f n b) (min n b) m (((2 ^ (fuel + 1) : ℕ) : ℤ) + 2) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have hx := ((IntegerRootsFN.Main.lemma_A_2).1 n b f hf m (((2 ^ (fuel + 1) : ℕ) : ℤ) + 2)
        (by
          have hp : (1 : ℕ) ≤ 2 ^ (fuel + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
          have hpZ : (1 : ℤ) ≤ ((2 ^ (fuel + 1) : ℕ) : ℤ) := by exact_mod_cast hp
          omega)).1 ht α hα
      have htri : ‖α - (m : ℂ)‖ ≤ ‖α - (r : ℂ)‖ + ‖(r : ℂ) - (m : ℂ)‖ := by
        convert norm_add_le (α - (r : ℂ)) ((r : ℂ) - (m : ℂ)) using 1 <;> abel
      have hnr : ‖α - (r : ℂ)‖ < 2 := by simpa [norm_sub_rev] using hnear
      have hdist : ‖(r : ℂ) - (m : ℂ)‖ ≤ (2 : ℝ) ^ (fuel + 1) := by
        have hreal : |(r - m : ℤ)| = ‖((r - m : ℤ) : ℂ)‖ := by
          rw [Complex.norm_intCast, Int.cast_abs]
        calc
          ‖(r : ℂ) - (m : ℂ)‖ = ‖((r - m : ℤ) : ℂ)‖ := by rw [Int.cast_sub]
          _ = |(r - m : ℤ)| := hreal.symm
          _ ≤ (2 : ℝ) ^ (fuel + 1) := by exact_mod_cast hrm
      norm_num [Nat.cast_pow] at hx ⊢
      linarith
    norm_num [Nat.cast_pow] at hnot
    have hmkept : m ∈ cs.filter (fun m =>
        !(testEmpty (truncate f n b) (min n b) m (((2 ^ (fuel + 1) : ℕ) : ℤ) + 2))) := by
      simp [List.mem_filter, hm, hnot]
    simp only [searchScales]
    rw [hnpow]
    apply ih
    have hchildren : (m - (2 ^ fuel : ℕ) : ℤ) ∈
        (cs.filter (fun m => !(testEmpty (truncate f n b) (min n b) m
          (((2 ^ (fuel + 1) : ℕ) : ℤ) + 2)))).flatMap
          (fun m => [m - ((2 ^ fuel : ℕ) : ℤ), m + ((2 ^ fuel : ℕ) : ℤ)]) := by
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨m, ?_, Or.inl rfl⟩
      simpa [Nat.cast_pow] using hmkept
    have hchildren₂ : (m + ((2 ^ fuel : ℕ) : ℤ)) ∈
        (cs.filter (fun m => !(testEmpty (truncate f n b) (min n b) m
          (((2 ^ (fuel + 1) : ℕ) : ℤ) + 2)))).flatMap
          (fun m => [m - ((2 ^ fuel : ℕ) : ℤ), m + ((2 ^ fuel : ℕ) : ℤ)]) := by
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨m, ?_, Or.inr rfl⟩
      simpa [Nat.cast_pow] using hmkept
    by_cases hrsign : m ≤ r
    · refine ⟨m + (2 ^ fuel : ℕ), hchildren₂, ?_⟩
      rw [hpow] at hrm
      have hboth := abs_le.mp hrm
      norm_num [Nat.cast_pow]
      apply abs_le.mpr
      constructor <;> omega
    · refine ⟨m - (2 ^ fuel : ℕ), hchildren, ?_⟩
      rw [hpow] at hrm
      have hboth := abs_le.mp hrm
      norm_num [Nat.cast_pow]
      apply abs_le.mpr
      constructor <;> omega

theorem solution :
    ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      ∀ r : ℤ, f.IsRoot r → 2 ≤ |r| → r ∈ searchCandidates f n b := by
  intro n b f hf r hr hlarge
  by_cases hd : min n b < n
  · obtain ⟨α, hα, hnear⟩ := IntegerRootsFN.Main.lemma_2_2 n b f hf hd r hr hlarge
    unfold searchCandidates
    apply coverage_aux n b f hf r α hα hnear
    refine ⟨0, by simp, ?_⟩
    simpa using integer_root_abs_le f n b hf r hr
  · have hdn : min n b = n := by omega
    have ht : truncate f n b = f := trunc_eq_of_min_eq f n b hdn hf.2.2.1
    unfold searchCandidates
    apply coverage_aux n b f hf r (r : ℂ) (by
      change (complexify (truncate f n b)).eval (r : ℂ) = 0
      rw [ht]
      change f.eval r = 0 at hr
      simpa [complexify] using congrArg (fun z : ℤ => (z : ℂ)) hr) (by simp)
    refine ⟨0, by simp, ?_⟩
    simpa using integer_root_abs_le f n b hf r hr
