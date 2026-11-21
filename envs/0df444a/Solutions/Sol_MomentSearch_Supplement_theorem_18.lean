-- Prove2me | solution 1 for MomentSearch.Supplement.theorem_18
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T01:17:24.519694+00:00
-- url     : https://prove2.me/submissions/0b856833-b9f0-426f-87b3-77d03bf7c7bb

import Mathlib
import Definitions.Def_MomentSearch_moment
import Definitions.Def_MomentSearch_Supplement_cdf
import Theorems.Thm_MomentSearch_Supplement_smoothed_step_certificate
open MomentSearch MomentSearch.Supplement
open scoped BigOperators

private lemma polynomial_expectation {n k : ℕ} (p π : Fin n → ℝ)
    (hm : ∀ i : ℕ, i ≤ k → moment p i = moment π i)
    (q : Polynomial ℝ) (hq : q.natDegree ≤ k) :
    ∑ t : Fin n, p t * q.eval (t.val : ℝ) = ∑ t : Fin n, π t * q.eval (t.val : ℝ) := by
  have heval (z : ℝ) : q.eval z = ∑ i ∈ Finset.range (k+1), q.coeff i * z^i :=
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hq) z
  have hexpand (u : Fin n → ℝ) :
      ∑ t : Fin n, u t * q.eval (t.val : ℝ) = ∑ i ∈ Finset.range (k+1), q.coeff i * moment u i := by
    simp only [heval, Finset.mul_sum, moment]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hexpand, hexpand]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hm i (by have := Finset.mem_range.mp hi; omega)]

private lemma window_count (n M W : ℕ) :
    (∑ t : Fin n, if M < t.val ∧ t.val < M+W then (1:ℝ) else 0) ≤ W := by
  classical
  have hc : (Finset.univ.filter (fun t : Fin n => M < t.val ∧ t.val < M+W)).card ≤ W := by
    calc
      _ ≤ (Finset.Ico M (M+W)).card := Finset.card_le_card_of_injOn (fun t : Fin n => t.val)
        (by intro t ht; have hh := (Finset.mem_filter.mp ht).2; exact Finset.mem_Ico.mpr ⟨hh.1.le, hh.2⟩)
        (by intro a _ b _ h; exact Fin.ext h)
      _ = W := by simp
  simpa [Finset.sum_ite] using (show ((Finset.univ.filter (fun t : Fin n => M < t.val ∧ t.val < M+W)).card : ℝ) ≤ W by exact_mod_cast hc)

private lemma grid_majorant (n k W : ℕ) (hn : 3 ≤ n) (hk : 16 ≤ k) (hWpos : 1 ≤ W)
    (hW : 96 * ((n:ℝ)/k) * Real.logb 2 n ≤ W) (M : Fin n) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ k ∧
      (∀ t : Fin n, (if t.val ≤ M.val then (1:ℝ) else 0) ≤ q.eval (t.val : ℝ)) ∧
      (∑ t : Fin n, (q.eval (t.val : ℝ) - (if t.val ≤ M.val then (1:ℝ) else 0))) ≤ 4 * W := by
  classical
  by_cases hhalf : 2*W ≤ n-1
  · by_cases hMW : M.val+W ≤ n-1
    · obtain ⟨q, hq, hnon, hone, hupper, htail⟩ :=
        smoothed_step_certificate n k M.val W hn hk hW hhalf hMW
      refine ⟨q, hq, ?_, ?_⟩
      · intro t; split_ifs with ht
        · exact hone t ht
        · exact hnon t
      · have hpoint (t : Fin n) :
            q.eval (t.val : ℝ) - (if t.val ≤ M.val then (1:ℝ) else 0) ≤
              (if M.val < t.val ∧ t.val < M.val+W then (1:ℝ) else 0) + 1/(n:ℝ)^2 := by
          by_cases ht : t.val ≤ M.val
          · simp only [if_pos ht, if_neg (show ¬ (M.val < t.val ∧ t.val < M.val+W) by omega), zero_add]
            linarith [hupper t]
          · by_cases htW : t.val < M.val+W
            · simp only [if_neg ht, if_pos (show M.val < t.val ∧ t.val < M.val+W from ⟨by omega, htW⟩), sub_zero]
              exact hupper t
            · simp only [if_neg ht, if_neg (show ¬ (M.val < t.val ∧ t.val < M.val+W) by omega), sub_zero, zero_add]
              exact htail t (by omega)
        have hs := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hpoint t)
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
        have hcount := window_count n M.val W
        have hnp : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
        have hnR : (1:ℝ)≤n := by exact_mod_cast (by omega : 1≤n)
        have herror : (n:ℝ)*(1/(n:ℝ)^2) ≤ 1 := by
          have heq : (n:ℝ)*(1/(n:ℝ)^2) = 1/(n:ℝ) := by field_simp
          rw [heq]
          exact (div_le_one hnp).2 hnR
        have hWR : (1:ℝ) ≤ W := by exact_mod_cast hWpos
        linarith
    · refine ⟨1, by simp, ?_, ?_⟩
      · intro t; simp only [Polynomial.eval_one]; split_ifs <;> norm_num
      · have hs : (∑ t : Fin n, ((1:ℝ) - (if t.val ≤ M.val then (1:ℝ) else 0))) ≤
            ∑ t : Fin n, if M.val < t.val ∧ t.val < M.val+W then (1:ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro t _
          have ht := t.isLt
          split_ifs <;> first | omega | norm_num
        simp only [Polynomial.eval_one]
        have hWR : (0:ℝ) ≤ W := Nat.cast_nonneg W
        linarith [window_count n M.val W]
  · refine ⟨1, by simp, ?_, ?_⟩
    · intro t; simp only [Polynomial.eval_one]; split_ifs <;> norm_num
    · simp only [Polynomial.eval_one]
      have hs : (∑ t : Fin n, ((1:ℝ) - (if t.val ≤ M.val then (1:ℝ) else 0))) ≤ (n:ℝ) := by
        calc
          _ ≤ ∑ _t : Fin n, (1:ℝ) := Finset.sum_le_sum (fun t _ => by split_ifs <;> norm_num)
          _ = _ := by simp
      have hbound : n ≤ 4*W := by omega
      exact hs.trans (by exact_mod_cast hbound)

private lemma grid_suffix_majorant (n k W : ℕ) (hn : 3 ≤ n) (hk : 16 ≤ k) (hWpos : 1 ≤ W)
    (hW : 96 * ((n:ℝ)/k) * Real.logb 2 n ≤ W) (M : Fin n) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ k ∧
      (∀ t : Fin n, (if M.val < t.val then (1:ℝ) else 0) ≤ q.eval (t.val : ℝ)) ∧
      (∑ t : Fin n, (q.eval (t.val : ℝ) - (if M.val < t.val then (1:ℝ) else 0))) ≤ 4 * W := by
  classical
  by_cases hlast : M.val = n-1
  · refine ⟨0, by simp, ?_, ?_⟩
    · intro t
      have ht : ¬ M.val < t.val := by have := t.isLt; omega
      simp [ht]
    · have ht : ∀ t : Fin n, ¬ M.val < t.val := by intro t; have := t.isLt; omega
      simp [ht]
  have hM := M.isLt
  let N : Fin n := ⟨n-2-M.val, by omega⟩
  obtain ⟨q, hq, hmajor, hsum⟩ := grid_majorant n k W hn hk hWpos hW N
  let a : Polynomial ℝ := Polynomial.C ((n-1:ℕ):ℝ) - Polynomial.X
  let r := q.comp a
  have hadeg : a.natDegree ≤ 1 := by
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hrdeg : r.natDegree ≤ k := by
    calc
      r.natDegree ≤ q.natDegree * a.natDegree := Polynomial.natDegree_comp_le
      _ ≤ k * 1 := Nat.mul_le_mul hq hadeg
      _ = k := Nat.mul_one k
  have heval (t : Fin n) : r.eval (t.val : ℝ) = q.eval (t.rev.val : ℝ) := by
    simp only [r, a, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
    congr 1
    have hnat : n-1-t.val = t.rev.val := by rw [Fin.val_rev]; omega
    rw [← hnat, Nat.cast_sub (by have := t.isLt; omega : t.val ≤ n-1)]
  have hind (t : Fin n) :
      (if t.rev.val ≤ N.val then (1:ℝ) else 0) = (if M.val < t.val then (1:ℝ) else 0) := by
    have ht := t.isLt
    have hh : t.rev.val ≤ N.val ↔ M.val < t.val := by
      simp only [N, Fin.val_rev]
      omega
    simp only [hh]
  refine ⟨r, hrdeg, ?_, ?_⟩
  · intro t
    rw [heval, ← hind]
    exact hmajor t.rev
  · simp_rw [heval, ← hind]
    have heq := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))
      (fun t => q.eval (t.val : ℝ) - (if t.val ≤ N.val then (1:ℝ) else 0))
    change (∑ t : Fin n, (q.eval (t.rev.val : ℝ) - (if t.rev.val ≤ N.val then (1:ℝ) else 0))) = _ at heq
    rw [heq]
    exact hsum

private lemma test_comparison {n k : ℕ} (p π : Fin n → ℝ)
    (hp : ∀ t, 0 ≤ p t) (_hπ : ∀ t, 0 ≤ π t) (L B : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ t, π t ≤ L) (hm : ∀ i : ℕ, i ≤ k → moment p i = moment π i)
    (f : Fin n → ℝ) (q : Polynomial ℝ) (hq : q.natDegree ≤ k)
    (hmajor : ∀ t, f t ≤ q.eval (t.val : ℝ))
    (hgap : (∑ t : Fin n, (q.eval (t.val : ℝ) - f t)) ≤ B) :
    (∑ t : Fin n, p t * f t) ≤ (∑ t : Fin n, π t * f t) + L*B := by
  have heq := polynomial_expectation p π hm q hq
  calc
    _ ≤ ∑ t : Fin n, p t * q.eval (t.val : ℝ) :=
      Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hmajor t) (hp t))
    _ = ∑ t : Fin n, π t * q.eval (t.val : ℝ) := heq
    _ = (∑ t : Fin n, π t * f t) + ∑ t : Fin n, π t * (q.eval (t.val : ℝ) - f t) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ (∑ t : Fin n, π t * f t) + L * ∑ t : Fin n, (q.eval (t.val : ℝ) - f t) := by
      gcongr
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_right (hbound t) (sub_nonneg.mpr (hmajor t)))
    _ ≤ _ := by gcongr

private lemma cdf_as_expectation {n : ℕ} (p : Fin n → ℝ) (M : Fin n) :
    cdf p M.val = ∑ t : Fin n, p t * (if t.val ≤ M.val then (1:ℝ) else 0) := by
  unfold cdf
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp

private lemma suffix_as_expectation {n : ℕ} (p : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (M : Fin n) :
    (∑ t : Fin n, p t * (if M.val < t.val then (1:ℝ) else 0)) = 1 - cdf p M.val := by
  conv_rhs => rw [← hp.2]
  rw [cdf, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> first | omega | ring

private lemma recovery_window (n k W : ℕ) (hn : 3 ≤ n) (hk : 16 ≤ k) (hWpos : 1 ≤ W)
    (hW : 96 * ((n:ℝ)/k) * Real.logb 2 n ≤ W)
    (L : ℝ) (π p : Fin n → ℝ) (hπ : π ∈ stdSimplex ℝ (Fin n)) (hp : p ∈ stdSimplex ℝ (Fin n))
    (hbound : ∀ t, π t ≤ L) (hm : ∀ i : ℕ, i ≤ k → moment p i = moment π i) :
    kolDist π p ≤ L * (4*W) := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hL : 0 ≤ L := (hπ.1 ⟨0, by omega⟩).trans (hbound _)
  apply ciSup_le
  intro M
  obtain ⟨q, hq, hmajor, hsum⟩ := grid_majorant n k W hn hk hWpos hW M
  have hu := test_comparison p π hp.1 hπ.1 L (4*W) hL hbound hm _ q hq hmajor hsum
  rw [← cdf_as_expectation p M, ← cdf_as_expectation π M] at hu
  obtain ⟨r, hr, hmajor', hsum'⟩ := grid_suffix_majorant n k W hn hk hWpos hW M
  have hl := test_comparison p π hp.1 hπ.1 L (4*W) hL hbound hm _ r hr hmajor' hsum'
  rw [suffix_as_expectation p hp M, suffix_as_expectation π hπ M] at hl
  rw [abs_le]
  constructor <;> linarith

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n k : ℕ), 16 ≤ k → k ≤ n → ∀ L : ℝ,
        ∀ π ∈ stdSimplex ℝ (Fin n), ∀ p ∈ stdSimplex ℝ (Fin n),
          (∀ t, π t ≤ L) → (∀ i : ℕ, i ≤ k → moment p i = moment π i) →
          kolDist π p ≤ C * (L * n / k) * Real.logb 2 n := by
  refine ⟨768, by norm_num, ?_⟩
  intro n k hk hkn L π hπ p hp hbound hm
  have hkp : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  have hfrac : 1 ≤ (n:ℝ)/k := (one_le_div hkp).2 (by exact_mod_cast hkn)
  have hlog : 1 ≤ Real.logb 2 n := by
    simpa using Real.logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2) hnR
  let A : ℝ := 96 * ((n:ℝ)/k) * Real.logb 2 n
  have hA : 1 ≤ A := by
    dsimp [A]
    nlinarith [mul_le_mul hfrac hlog (by norm_num : (0:ℝ) ≤ 1) (by linarith : 0 ≤ (n:ℝ)/k)]
  let W : ℕ := ⌈A⌉₊
  have hWpos : 1 ≤ W := Nat.one_le_ceil_iff.mpr (by linarith)
  have hW : A ≤ (W:ℝ) := Nat.le_ceil _
  have hWupper : (W:ℝ) ≤ 2*A := by
    have hc := Nat.ceil_lt_add_one (by linarith : 0 ≤ A)
    dsimp [W]
    linarith
  have hL : 0 ≤ L := (hπ.1 ⟨0, by omega⟩).trans (hbound _)
  calc
    kolDist π p ≤ L * (4*W) := recovery_window n k W (by omega) hk hWpos hW L π p hπ hp hbound hm
    _ ≤ L * (4*(2*A)) := mul_le_mul_of_nonneg_left (by linarith) hL
    _ = 768 * (L*n/k) * Real.logb 2 n := by dsimp [A]; ring
