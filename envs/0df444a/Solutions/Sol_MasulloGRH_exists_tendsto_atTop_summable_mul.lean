-- Prove2me | solution 1 for MasulloGRH.exists_tendsto_atTop_summable_mul
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:29:38.459679+00:00
-- url     : https://prove2.me/submissions/3277203c-3b56-4a59-9ab8-b706bbf03c32

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open Filter Topology

theorem solution (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hc : Summable c) :
    ∃ μ : ℕ → ℝ, (∀ n, 1 ≤ μ n) ∧ Filter.Tendsto μ Filter.atTop Filter.atTop ∧
      Summable (fun n => c n * μ n) := by
  set r : ℕ → ℝ := fun n => ∑' k, c (k + n) + (1 / 2 : ℝ) ^ n with hr
  have hrpos : ∀ n, 0 < r n := fun n => by
    have : 0 ≤ ∑' k, c (k + n) := tsum_nonneg fun k => hc0 _
    have : (0 : ℝ) < (1 / 2) ^ n := by positivity
    simp only [hr]; linarith
  have hstep : ∀ n, c n ≤ r n - r (n + 1) := fun n => by
    have hs : Summable (fun k => c (k + n)) := (summable_nat_add_iff n).2 hc
    have h1 := hs.tsum_eq_zero_add
    simp only [zero_add] at h1
    have h2 : ∀ k, c (k + 1 + n) = c (k + (n + 1)) := fun k => by ring_nf
    simp only [h2] at h1
    simp only [hr, h1, pow_succ]
    have : (0 : ℝ) < (1 / 2) ^ n := by positivity
    nlinarith
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ∑' k, c (k + n)) atTop (𝓝 0) := tendsto_sum_nat_add c
    have h2 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have := h1.add h2
    rw [add_zero] at this
    exact this
  refine ⟨fun n => 1 + 1 / Real.sqrt (r n), fun n => ?_, ?_, ?_⟩
  · have : 0 ≤ 1 / Real.sqrt (r n) := by positivity
    linarith
  · apply tendsto_atTop_add_const_left
    have hs : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.2
      refine ⟨?_, Eventually.of_forall fun n => Real.sqrt_pos.2 (hrpos n)⟩
      have := (Real.continuous_sqrt.tendsto 0).comp hr0
      rw [Real.sqrt_zero] at this
      exact this
    have := tendsto_inv_nhdsGT_zero.comp hs
    simp only [one_div]
    exact this
  · have hg0 : ∀ n, 0 ≤ c n / Real.sqrt (r n) := fun n => div_nonneg (hc0 n) (Real.sqrt_nonneg _)
    have hbound : ∀ n, c n / Real.sqrt (r n) ≤
        2 * (Real.sqrt (r n) - Real.sqrt (r (n + 1))) := fun n => by
      have ha := Real.sqrt_pos.2 (hrpos n)
      have hb := Real.sqrt_nonneg (r (n + 1))
      have hA := Real.sq_sqrt (hrpos n).le
      have hB := Real.sq_sqrt (hrpos (n + 1)).le
      have hs := hstep n
      have hcn := hc0 n
      rw [div_le_iff₀ ha]
      have hba : Real.sqrt (r (n + 1)) ≤ Real.sqrt (r n) := by nlinarith
      nlinarith
    have hsum : Summable (fun n => c n / Real.sqrt (r n)) := by
      refine summable_of_sum_range_le hg0 (c := 2 * Real.sqrt (r 0)) fun N => ?_
      calc ∑ i ∈ Finset.range N, c i / Real.sqrt (r i)
          ≤ ∑ i ∈ Finset.range N, 2 * (Real.sqrt (r i) - Real.sqrt (r (i + 1))) :=
            Finset.sum_le_sum fun i _ => hbound i
        _ = 2 * (Real.sqrt (r 0) - Real.sqrt (r N)) := by
            rw [← Finset.mul_sum, Finset.sum_range_sub']
        _ ≤ 2 * Real.sqrt (r 0) := by nlinarith [Real.sqrt_nonneg (r N)]
    have := hc.add hsum
    refine this.congr fun n => ?_
    simp only
    ring
