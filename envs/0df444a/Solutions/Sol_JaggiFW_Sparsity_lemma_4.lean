-- Prove2me | solution 1 for JaggiFW.Sparsity.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:50:37.325714+00:00
-- url     : https://prove2.me/submissions/ff7753f8-95d8-41cf-94e4-7f9cf4e97293

import Mathlib
import Definitions.Def_JaggiFW_Sparsity_Setting

open JaggiFW.Sparsity

private lemma derivative_sqNorm {n : ℕ} (x h : Fin n → ℝ) :
    fderiv ℝ sqNorm x h = ∑ i, 2 * x i * h i := by
  have hd := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
    (fun i _ => (hasFDerivAt_apply (𝕜 := ℝ) i x).pow 2)
  change HasFDerivAt sqNorm _ x at hd
  rw [hd.fderiv]
  simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, nsmul_eq_mul]
private lemma sparse_lower {n : ℕ} (k : ℕ) (hk : 0 < k)
    (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) (hc : card x ≤ k) :
    1 / (k : ℝ) ≤ sqNorm x := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i => x i ≠ 0
  have hsum : ∑ i ∈ s, x i = 1 := by
    calc
      _ = ∑ i, x i := Finset.sum_subset (Finset.filter_subset _ _) (by
        intro i _ hi
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
        exact hi)
      _ = 1 := hx.2
  have hsq : ∑ i ∈ s, x i ^ 2 = sqNorm x := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    simp [hi]
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := x)
  rw [hsum, hsq, one_pow] at hcs
  have hcard : (s.card : ℝ) ≤ k := by exact_mod_cast hc
  have hnonneg : 0 ≤ sqNorm x := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have hbound := hcs.trans (mul_le_mul_of_nonneg_right hcard hnonneg)
  apply (div_le_iff₀ (by exact_mod_cast hk : (0 : ℝ) < k)).2
  nlinarith

theorem solution {n : ℕ} (k : ℕ) (hk : k < n) :
    ∀ x ∈ stdSimplex ℝ (Fin n), card x ≤ k →
      2 / (k : ℝ) ≤ dualityGap sqNorm (stdSimplex ℝ (Fin n)) x := by
  classical
  intro x hx hc
  have hnonzero : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    have hsum := hx.2
    simp [h] at hsum
  have hkpos : 0 < k := by
    obtain ⟨i, hi⟩ := hnonzero
    have hcard : 0 < card x := Finset.card_pos.mpr ⟨i, by simp [hi]⟩
    omega
  obtain ⟨i, hi⟩ : ∃ i, x i = 0 := by
    by_contra h
    push_neg at h
    have hcard : card x = n := by simp [card, h]
    omega
  have hlower := sparse_lower k hkpos x hx hc
  have hbdd : BddAbove ((fun s => fderiv ℝ sqNorm x (x - s)) ''
      stdSimplex ℝ (Fin n)) :=
    ((isCompact_stdSimplex ℝ (Fin n)).image
      ((fderiv ℝ sqNorm x).continuous.comp (continuous_const.sub continuous_id))).bddAbove
  have hvalue : fderiv ℝ sqNorm x (x - Pi.single i 1) = 2 * sqNorm x := by
    rw [derivative_sqNorm]
    simp only [sqNorm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [Pi.sub_apply, Pi.single_apply, hji, pow_two, mul_assoc]
  have hgap : 2 * sqNorm x ≤ dualityGap sqNorm (stdSimplex ℝ (Fin n)) x := by
    rw [dualityGap]
    rw [← hvalue]
    apply le_csSup hbdd
    exact ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, rfl⟩
  calc
    2 / (k : ℝ) = 2 * (1 / (k : ℝ)) := by ring
    _ ≤ 2 * sqNorm x := mul_le_mul_of_nonneg_left hlower (by norm_num)
    _ ≤ _ := hgap