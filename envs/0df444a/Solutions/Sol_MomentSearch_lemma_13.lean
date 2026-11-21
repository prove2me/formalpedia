-- Prove2me | solution 1 for MomentSearch.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:09:44.126434+00:00
-- url     : https://prove2.me/submissions/c6661e54-0cb4-4039-ace3-df3b957c427a

import Mathlib
import Definitions.Def_MomentSearch_grid
import Theorems.Thm_MomentSearch_theorem_24

open MomentSearch

theorem solution :
    ∃ C₁ : ℝ, ∀ n k : ℕ, 2 ≤ n → (k : ℝ) ≤ ((n : ℝ) - 1) / 2 →
      ∀ q : Polynomial ℝ, q.natDegree ≤ k →
      (∀ t : Fin n, |q.eval (grid n (t : ℕ))| ≤ 1) →
      ∀ x ∈ Set.Icc (-(3 / 4 : ℝ)) (3 / 4), |q.eval x| ≤ C₁ := by
  obtain ⟨C, hC⟩ := MomentSearch.theorem_24
  let K := Real.logb 2 (Real.pi / Real.arctan (1 / 2))
  refine ⟨max 1 (max 0 C * K), ?_⟩
  intro n k hn hk q hq hg x hx
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hd : 0 < (n : ℝ) - 1 := by linarith
  by_cases hkz : k = 0
  · have heq := Polynomial.eq_C_of_natDegree_le_zero (hkz ▸ hq)
    have ht := hg (⟨0, by omega⟩ : Fin n)
    rw [heq, Polynomial.eval_C] at ht ⊢
    exact ht.trans (le_max_left _ _)
  have hknat : 1 ≤ k := by omega
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hklt : k < n := by
    have h : (k : ℝ) < n := by linarith
    exact_mod_cast h
  let α : ℝ := (n : ℝ) / ((n : ℝ) - 1)
  let β : ℝ := ((n : ℝ) - 1) / (n : ℝ)
  have hα : 0 < α := div_pos hnpos hd
  have hβ : 0 ≤ β := (div_pos hd hnpos).le
  have hβ1 : β ≤ 1 := (div_le_iff₀ hnpos).2 (by linarith)
  let Q := q.comp (Polynomial.C α * Polynomial.X)
  have hQ : Q.natDegree ≤ k := by
    refine Polynomial.natDegree_comp_le.trans ?_
    simpa [Polynomial.natDegree_C_mul_X α hα.ne'] using hq
  have hEval (z : ℝ) : Q.eval z = q.eval (α * z) := by simp [Q]
  have hgrid (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
      |Q.eval (-1 + (2 * (j : ℝ) - 1) / (n : ℝ))| ≤ 1 := by
    let t : Fin n := ⟨j - 1, by omega⟩
    have ht : ((t : ℕ) : ℝ) = (j : ℝ) - 1 := by
      change ((j - 1 : ℕ) : ℝ) = _
      rw [Nat.cast_sub hj, Nat.cast_one]
    rw [hEval]
    have he : α * (-1 + (2 * (j : ℝ) - 1) / (n : ℝ)) = grid n (t : ℕ) := by
      unfold grid
      rw [ht]
      dsimp [α]
      field_simp [hnpos.ne', hd.ne']
      ring
    rw [he]
    exact hg t
  let y := β * x
  have hyEval : Q.eval y = q.eval x := by
    rw [hEval]
    congr 1
    dsimp [y, α, β]
    field_simp [hnpos.ne', hd.ne']
  have hy : |y| ≤ 3 / 4 := by
    dsimp [y]
    rw [abs_mul, abs_of_nonneg hβ]
    exact (mul_le_of_le_one_left (abs_nonneg _) hβ1).trans (abs_le.mpr hx)
  have hy2 : y ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by
    rw [← sq_abs y]
    exact (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hy
  have hfrac : (k : ℝ) / n ≤ 1 / 2 := (div_le_iff₀ hnpos).2 (by linarith)
  have hfrac2 : (k : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    rw [← div_pow]
    exact (sq_le_sq₀ (by positivity) (by norm_num)).2 hfrac
  let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (n : ℝ) ^ 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 1 - (k : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
    Real.sq_sqrt (by linarith)
  have hgap : (3 / 16 : ℝ) ≤ r ^ 2 - y ^ 2 := by linarith
  have hyin : |y| < r := by
    apply (sq_lt_sq₀ (abs_nonneg _) hr0).1
    rw [sq_abs]
    linarith
  obtain ⟨hyl, hyr⟩ := abs_lt.mp hyin
  have hmain := hC n k hknat hklt Q hQ hgrid r rfl y hyl hyr
  let z := (n : ℝ) / k * Real.sqrt (r ^ 2 - y ^ 2)
  have hsqrt : (1 / 4 : ℝ) ≤ Real.sqrt (r ^ 2 - y ^ 2) := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt (by linarith)]
    linarith
  have hratio : (2 : ℝ) ≤ (n : ℝ) / k := (le_div_iff₀ hkpos).2 (by linarith)
  have hz : (1 / 2 : ℝ) ≤ z := by
    have hh := mul_le_mul hratio hsqrt (by norm_num) (by positivity)
    norm_num at hh
    exact hh
  have ha : Real.arctan (1 / 2) ≤ Real.arctan z := Real.arctan_le_arctan_iff.mpr hz
  have ha0 : 0 < Real.arctan (1 / 2) := Real.arctan_pos.mpr (by norm_num)
  have haz : 0 < Real.arctan z := ha0.trans_le ha
  have hlog : Real.logb 2 (Real.pi / Real.arctan z) ≤ K :=
    Real.logb_le_logb_of_le (by norm_num) (div_pos Real.pi_pos haz)
      (div_le_div_of_nonneg_left Real.pi_pos.le ha0 ha)
  have hlog0 : 0 ≤ Real.logb 2 (Real.pi / Real.arctan z) := by
    apply Real.logb_nonneg (by norm_num)
    apply (le_div_iff₀ haz).2
    have h := Real.arctan_lt_pi_div_two z
    linarith [Real.pi_pos]
  calc
    |q.eval x| = |Q.eval y| := by rw [hyEval]
    _ ≤ C * Real.logb 2 (Real.pi / Real.arctan z) := hmain
    _ ≤ max 0 C * Real.logb 2 (Real.pi / Real.arctan z) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hlog0
    _ ≤ max 0 C * K := mul_le_mul_of_nonneg_left hlog (le_max_left _ _)
    _ ≤ max 1 (max 0 C * K) := le_max_right _ _
