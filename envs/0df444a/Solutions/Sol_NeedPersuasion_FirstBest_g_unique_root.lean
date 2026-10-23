-- Prove2me | solution 1 for NeedPersuasion.FirstBest.g_unique_root
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:38:30.993663+00:00
-- url     : https://prove2.me/submissions/d9ce52f3-9290-4a42-b416-5faf35bad0a2

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model
import Definitions.Def_NeedPersuasion_FirstBest_Objects

open NeedPersuasion.FirstBest

set_option linter.unusedSectionVars false

namespace NPGRoot

section
variable (M : Model) (hM : M.Standing)
include hM

lemma d_neg (k : ℕ) : M.uL (k + 1) - M.uL k < 0 := by
  obtain ⟨-, -, -, -, -, -, -, hA, -, -⟩ := hM
  have := hA (Nat.lt_succ_self k); linarith

lemma d_ge (k : ℕ) : -(M.uL 0 - M.uL 1) ≤ M.uL (k + 1) - M.uL k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hC⟩ := hM
  have := hC (Nat.zero_le k); simp only at this; linarith

lemma abs_d_le (k : ℕ) : |M.uL (k + 1) - M.uL k| ≤ M.uL 0 - M.uL 1 := by
  rw [abs_le]; exact ⟨d_ge M hM k, by linarith [d_neg M hM k, d_neg M hM 0]⟩

lemma abs_uL_le (n : ℕ) : |M.uL n| ≤ |M.uL 0| + n * (M.uL 0 - M.uL 1) := by
  have hD : 0 ≤ M.uL 0 - M.uL 1 := by linarith [d_neg M hM 0]
  have hup : M.uL n ≤ M.uL 0 := by
    obtain ⟨-, -, -, -, -, -, -, hA, -, -⟩ := hM
    exact hA.antitone (Nat.zero_le n)
  have hlo : M.uL 0 - n * (M.uL 0 - M.uL 1) ≤ M.uL n := by
    induction n with
    | zero => simp
    | succ k ih =>
      have := d_ge M hM k
      push_cast
      have hk : M.uL k ≤ M.uL 0 := by
        obtain ⟨-, -, -, -, -, -, -, hA, -, -⟩ := hM
        exact hA.antitone (Nat.zero_le k)
      linarith [ih hk]
  rw [abs_le]
  have h0 : (0 : ℝ) ≤ n * (M.uL 0 - M.uL 1) := mul_nonneg (Nat.cast_nonneg n) hD
  constructor
  · have := neg_abs_le (M.uL 0); linarith
  · have := le_abs_self (M.uL 0); linarith

lemma summ_pow (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) : Summable (fun k => x ^ k * M.uL k) := by
  have hs1 : Summable (fun n : ℕ => x ^ n) := summable_geometric_of_lt_one hx0 hx1
  have hs2 : Summable (fun n : ℕ => (n : ℝ) ^ 1 * x ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)
  refine Summable.of_norm_bounded ((hs1.mul_left |M.uL 0|).add (hs2.mul_left (M.uL 0 - M.uL 1)))
    (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 n)]
  have := mul_le_mul_of_nonneg_left (abs_uL_le M hM n) (pow_nonneg hx0 n)
  simp only [pow_one]
  nlinarith

lemma summ_d (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun k => x ^ (k + 1) * (M.uL (k + 1) - M.uL k)) := by
  have hs1 : Summable (fun n : ℕ => x ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hx0 hx1)
  refine Summable.of_norm_bounded (hs1.mul_left (M.uL 0 - M.uL 1)) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 _)]
  have := mul_le_mul_of_nonneg_left (abs_d_le M hM n) (pow_nonneg hx0 (n + 1))
  linarith

lemma g_rep (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    g M x = M.uL 0 + ∑' k, x ^ (k + 1) * (M.uL (k + 1) - M.uL k) := by
  have hS := summ_pow M hM x hx0 hx1
  have hS1 : Summable (fun k => x ^ (k + 1) * M.uL (k + 1)) := (summable_nat_add_iff 1).mpr hS
  have hT : Summable (fun k => x ^ (k + 1) * M.uL k) :=
    (hS.mul_left x).congr (fun k => by ring)
  unfold g
  have e1 : (fun k => (1 - x) * x ^ k * M.uL k) = fun k => x ^ k * M.uL k - x ^ (k + 1) * M.uL k := by
    ext k; ring
  have e2 : (fun k => x ^ (k + 1) * (M.uL (k + 1) - M.uL k)) =
      fun k => x ^ (k + 1) * M.uL (k + 1) - x ^ (k + 1) * M.uL k := by
    ext k; ring
  rw [e1, e2, hS.tsum_sub hT, hS1.tsum_sub hT, hS.tsum_eq_zero_add]
  simp only [pow_zero, one_mul]
  ring

lemma g_strictAnti : StrictAntiOn (g M) (Set.Ico 0 1) := by
  intro x hx y hy hxy
  rw [g_rep M hM x hx.1 hx.2, g_rep M hM y hy.1 hy.2]
  have hlt : ∑' k, y ^ (k + 1) * (M.uL (k + 1) - M.uL k) <
      ∑' k, x ^ (k + 1) * (M.uL (k + 1) - M.uL k) := by
    refine Summable.tsum_lt_tsum (i := 0) (fun k => ?_) ?_ (summ_d M hM y hy.1 hy.2)
      (summ_d M hM x hx.1 hx.2)
    · apply mul_le_mul_of_nonpos_right _ (d_neg M hM k).le
      exact pow_le_pow_left₀ hx.1 hxy.le _
    · simp only [zero_add, pow_one]
      exact mul_lt_mul_of_neg_right hxy (d_neg M hM 0)
  linarith

end

end NPGRoot

open NPGRoot in
theorem solution (M : Model) (hM : M.Standing) :
    StrictAntiOn (g M) (Set.Ico 0 1) ∧ ∃! Λ : ℝ, Λ ∈ Set.Ioo (0 : ℝ) 1 ∧ g M Λ = 0 := by
  have hanti := g_strictAnti M hM
  refine ⟨hanti, ?_⟩
  have hu0 : 0 < M.uL 0 := hM.2.2.2.1
  obtain ⟨K, hK⟩ := hM.2.2.2.2.2.1
  have hK1 : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; linarith
    · exact h
  -- g 0 > 0
  have hg0 : g M 0 = M.uL 0 := by rw [g_rep M hM 0 le_rfl one_pos]; simp
  -- an upper bound for g
  have hbound : ∀ x, 0 ≤ x → x < 1 → g M x ≤ M.uL 0 + x ^ K * (M.uL K - M.uL 0) := by
    intro x hx0 hx1
    rw [g_rep M hM x hx0 hx1]
    have hs := summ_d M hM x hx0 hx1
    rw [← hs.sum_add_tsum_nat_add K]
    have htail : ∑' k, x ^ (k + K + 1) * (M.uL (k + K + 1) - M.uL (k + K)) ≤ 0 :=
      tsum_nonpos (fun k => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx0 _)
        (d_neg M hM (k + K)).le)
    have hfin : ∑ k ∈ Finset.range K, x ^ (k + 1) * (M.uL (k + 1) - M.uL k) ≤
        ∑ k ∈ Finset.range K, x ^ K * (M.uL (k + 1) - M.uL k) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_range] at hk
      apply mul_le_mul_of_nonpos_right _ (d_neg M hM k).le
      exact pow_le_pow_of_le_one hx0 hx1.le (by omega)
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => M.uL k)] at hfin
    linarith
  -- a point x0 < 1 with g x0 < 0
  set c := M.uL 0 / (M.uL 0 - M.uL K) with hc
  have hden : 0 < M.uL 0 - M.uL K := by linarith
  have hc0 : 0 < c := div_pos hu0 hden
  have hc1 : c < 1 := by rw [hc, div_lt_one hden]; linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  set t := (1 - c) / (2 * K) with ht
  have ht0 : 0 < t := div_pos (by linarith) (by positivity)
  have htK : (K : ℝ) * t = (1 - c) / 2 := by rw [ht]; field_simp
  have ht1 : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    nlinarith
  set x0 := 1 - t with hx0
  have hx00 : 0 ≤ x0 := by linarith
  have hx01 : x0 < 1 := by linarith
  have hpow : c < x0 ^ K := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -t by linarith) K
    rw [show (1 : ℝ) + -t = x0 by rw [hx0]; ring] at this
    nlinarith
  have hgx0 : g M x0 < 0 := by
    have h1 := hbound x0 hx00 hx01
    have h2 : x0 ^ K * (M.uL K - M.uL 0) < c * (M.uL K - M.uL 0) :=
      mul_lt_mul_of_neg_right hpow (by linarith)
    have h3 : c * (M.uL K - M.uL 0) = - M.uL 0 := by
      rw [hc]; field_simp; ring
    linarith
  -- continuity of g on [0, x0]
  have hcont : ContinuousOn (g M) (Set.Icc 0 x0) := by
    have hc' : ContinuousOn (fun x => M.uL 0 + ∑' k, x ^ (k + 1) * (M.uL (k + 1) - M.uL k))
        (Set.Icc 0 x0) := by
      apply ContinuousOn.add continuousOn_const
      refine continuousOn_tsum (u := fun k => x0 ^ (k + 1) * (M.uL 0 - M.uL 1))
        (fun k => by fun_prop) ?_ ?_
      · exact ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hx00 hx01)).mul_right _
      · intro k x hx
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx.1 _)]
        exact mul_le_mul (pow_le_pow_left₀ hx.1 hx.2 _) (abs_d_le M hM k) (abs_nonneg _)
          (pow_nonneg hx00 _)
    refine hc'.congr (fun x hx => ?_)
    exact g_rep M hM x hx.1 (lt_of_le_of_lt hx.2 hx01)
  have hivt := intermediate_value_Icc' hx00 hcont
  have h0mem : (0 : ℝ) ∈ Set.Icc (g M x0) (g M 0) := ⟨hgx0.le, by rw [hg0]; exact hu0.le⟩
  obtain ⟨Λ, hΛI, hΛ⟩ := hivt h0mem
  have hΛpos : 0 < Λ := by
    rcases hΛI.1.lt_or_eq with h | h
    · exact h
    · rw [← h, hg0] at hΛ; linarith
  refine ⟨Λ, ⟨⟨hΛpos, lt_of_le_of_lt hΛI.2 hx01⟩, hΛ⟩, ?_⟩
  rintro μ ⟨hμI, hμ⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hanti ⟨hμI.1.le, hμI.2⟩ ⟨hΛpos.le, lt_of_le_of_lt hΛI.2 hx01⟩ h
    linarith
  · have := hanti ⟨hΛpos.le, lt_of_le_of_lt hΛI.2 hx01⟩ ⟨hμI.1.le, hμI.2⟩ h
    linarith
