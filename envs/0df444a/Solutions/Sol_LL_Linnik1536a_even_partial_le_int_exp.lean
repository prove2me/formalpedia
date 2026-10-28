-- Prove2me | solution 1 for LL_Linnik1536a.even_partial_le_int_exp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:56:01.956967+00:00
-- url     : https://prove2.me/submissions/301aacc3-5247-429a-8ff9-5dce088a1667

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
open Real MeasureTheory Finset

namespace A3S89LLp

noncomputable def T (N : ℕ) (y : ℝ) : ℝ := ∑ n ∈ range N, y ^ n / (n.factorial : ℝ)

lemma hasDerivAt_T (N : ℕ) (y : ℝ) : HasDerivAt (T (N + 1)) (T N y) y := by
  induction N with
  | zero =>
    have : T 1 = fun _ => 1 := by funext z; simp [T]
    rw [this]; simpa [T] using hasDerivAt_const y (1 : ℝ)
  | succ N ih =>
    have h1 : T (N + 2) = fun z => T (N + 1) z + z ^ (N + 1) / ((N + 1).factorial : ℝ) := by
      funext z; simp only [T]; rw [sum_range_succ]
    have hp : HasDerivAt (fun z : ℝ => z ^ (N + 1) / ((N + 1).factorial : ℝ))
        (((N + 1 : ℕ) : ℝ) * y ^ N / ((N + 1).factorial : ℝ)) y := by
      have := (hasDerivAt_pow (N + 1) y).div_const ((N + 1).factorial : ℝ)
      simpa using this
    rw [h1]
    refine (ih.add hp).congr_deriv ?_
    unfold T; rw [sum_range_succ (n := N)]
    congr 1
    rw [Nat.factorial_succ]; push_cast
    have : (N.factorial : ℝ) ≠ 0 := by positivity
    field_simp

lemma T_zero (N : ℕ) : T (N + 1) 0 = 1 := by
  simp only [T]
  rw [sum_range_succ']
  simp

lemma neg_case (N : ℕ) : ∀ y ≤ 0, 0 ≤ (-1 : ℝ) ^ N * (exp y - T N y) := by
  induction N with
  | zero => intro y _; simp [T]; positivity
  | succ N ih =>
    intro y hy
    set g : ℝ → ℝ := fun z => (-1 : ℝ) ^ (N + 1) * (exp z - T (N + 1) z) with hg
    have hd : ∀ z, HasDerivAt g ((-1 : ℝ) ^ (N + 1) * (exp z - T N z)) z := fun z =>
      ((Real.hasDerivAt_exp z).sub (hasDerivAt_T N z)).const_mul _
    have hanti : AntitoneOn g (Set.Iic 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
      · exact (continuous_iff_continuousAt.2 fun z => (hd z).continuousAt).continuousOn
      · exact fun z _ => (hd z).differentiableAt.differentiableWithinAt
      · intro z hz
        rw [(hd z).deriv]
        rw [interior_Iic] at hz
        have := ih z (le_of_lt hz)
        rw [pow_succ]; nlinarith
    have h0 : g 0 = 0 := by simp [hg, T_zero]
    have := hanti (Set.mem_Iic.2 hy) (Set.mem_Iic.2 le_rfl) hy
    rw [h0] at this; exact this

lemma T_le_exp (m : ℕ) (y : ℝ) : T (2 * m) y ≤ exp y := by
  rcases le_total 0 y with h | h
  · exact Real.sum_le_exp_of_nonneg h _
  · have := neg_case (2 * m) y h
    rw [pow_mul] at this; norm_num at this; linarith

lemma split_sum (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a (2 * j + 1)) (K : ℕ) :
    ∑ j ∈ range K, a (2 * j) ≤ ∑ n ∈ range (2 * K), a n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, show 2 * (K + 1) = 2 * K + 1 + 1 by ring, sum_range_succ,
      sum_range_succ]
    linarith [ha K]

end A3S89LLp

theorem solution {f : ℝ → ℝ} (hf : Continuous f)
    (hmom : ∀ n : ℕ, 0 ≤ ∫ x in (0 : ℝ)..1, f x ^ n) {lam : ℝ} (hlam : 0 ≤ lam) (K : ℕ) :
    ∑ j ∈ range K, lam ^ (2 * j) / ((2 * j).factorial : ℝ) * ∫ x in (0 : ℝ)..1, f x ^ (2 * j) ≤
      ∫ x in (0 : ℝ)..1, Real.exp (lam * f x) := by
  set a : ℕ → ℝ := fun n => lam ^ n / (n.factorial : ℝ) * ∫ x in (0 : ℝ)..1, f x ^ n with ha
  have h1 : ∑ j ∈ range K, a (2 * j) ≤ ∑ n ∈ range (2 * K), a n :=
    A3S89LLp.split_sum a (fun j => mul_nonneg (by positivity) (hmom _)) K
  have h2 : ∑ n ∈ range (2 * K), a n = ∫ x in (0 : ℝ)..1, A3S89LLp.T (2 * K) (lam * f x) := by
    simp only [A3S89LLp.T]
    rw [intervalIntegral.integral_finsetSum]
    · refine sum_congr rfl fun n _ => ?_
      simp only [ha]
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext x; rw [mul_pow]; ring
    · intro n _
      exact ((hf.const_mul lam).pow n |>.div_const _).intervalIntegrable _ _
  have h3 : ∫ x in (0 : ℝ)..1, A3S89LLp.T (2 * K) (lam * f x) ≤ ∫ x in (0 : ℝ)..1, exp (lam * f x) := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · simp only [A3S89LLp.T]
      exact (continuous_finsetSum _ fun n _ =>
        ((hf.const_mul lam).pow n).div_const _).intervalIntegrable _ _
    · exact (Real.continuous_exp.comp (hf.const_mul lam)).intervalIntegrable _ _
    · intro x _; exact A3S89LLp.T_le_exp K _
  have : ∑ j ∈ range K, lam ^ (2 * j) / ((2 * j).factorial : ℝ) *
      ∫ x in (0 : ℝ)..1, f x ^ (2 * j) = ∑ j ∈ range K, a (2 * j) := rfl
  rw [this]; linarith
