-- Prove2me | solution 1 for LargeDelaySGD.MeanSquare.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:22:02.988523+00:00
-- url     : https://prove2.me/submissions/7b5689c8-d9bb-4ca3-af0c-b3424c8a6a03

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model

open MeasureTheory ProbabilityTheory

namespace Aux_LDSGD_A4

lemma freq (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hsa : ¬ Summable a)
    (hsab : Summable (fun n => a n * b n)) (ε : ℝ) (hε : 0 < ε) (M : ℕ) :
    ∃ k, M ≤ k ∧ b k < ε := by
  by_contra hcon
  push_neg at hcon
  apply hsa
  have h0 : Summable (fun n => a (n + M) * b (n + M)) := (summable_nat_add_iff M).mpr hsab
  have h1 : Summable (fun n => a (n + M) * b (n + M) / ε) := h0.div_const ε
  have h2 : Summable (fun n => a (n + M)) := by
    refine Summable.of_nonneg_of_le (fun n => ha _) (fun n => ?_) h1
    rw [le_div_iff₀ hε]
    have := hcon (n + M) (by omega)
    nlinarith [ha (n + M)]
  exact (summable_nat_add_iff M).mp h2

lemma tail (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hf : Summable f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → ∀ k, ∑ i ∈ Finset.Ico n k, f i < δ := by
  have ht := tendsto_sum_nat_add f
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn k => ?_⟩
  have hs : Summable (fun j => f (j + n)) := (summable_nat_add_iff n).mpr hf
  calc ∑ i ∈ Finset.Ico n k, f i = ∑ j ∈ Finset.range (k - n), f (j + n) := by
        rw [Finset.sum_Ico_eq_sum_range]
        exact Finset.sum_congr rfl (fun j _ => by rw [add_comm])
    _ ≤ ∑' j, f (j + n) := hs.sum_le_tsum _ (fun j _ => hf0 _)
    _ < δ := hN n hn

end Aux_LDSGD_A4

open LargeDelaySGD.MeanSquare Aux_LDSGD_A4 in
theorem solution (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hsa : ¬ Summable a) (hsab : Summable (fun n => a n * b n))
    (K : ℝ) (hK : 0 < K) (hinc : ∀ n, |b (n + 1) - b n| ≤ K * a n) :
    Filter.Tendsto b Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ε / 2 := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; positivity
  have hδ : 0 < e ^ 2 / K := by positivity
  obtain ⟨N, hN⟩ := tail (fun n => a n * b n) (fun n => mul_nonneg (ha n) (hb n)) hsab
    (e ^ 2 / K) hδ
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hb n)]
  by_contra hcon
  push_neg at hcon
  have hex : ∃ k, n ≤ k ∧ b k < e := freq a b ha hsa hsab e he0 n
  classical
  obtain ⟨k0, hk0, hmin'⟩ : ∃ k0, (n ≤ k0 ∧ b k0 < e) ∧ ∀ i < k0, ¬ (n ≤ i ∧ b i < e) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hmin : ∀ i, n ≤ i → i < k0 → e ≤ b i := by
    intro i hi1 hi2
    by_contra h
    push_neg at h
    exact hmin' i hi2 ⟨hi1, h⟩
  have key : ∀ m, n ≤ m → m ≤ k0 →
      e * (b n - b m) ≤ K * ∑ i ∈ Finset.Ico n m, a i * b i := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => intro _; simp
    | succ m hm ih =>
      intro hmk
      have h1 := ih (by omega)
      have h2 := hmin m hm (by omega)
      have h3 : b m - b (m + 1) ≤ K * a m := by
        have := hinc m
        rw [abs_le] at this
        linarith [this.1]
      rw [Finset.sum_Ico_succ_top hm]
      nlinarith [mul_le_mul_of_nonneg_left h3 he0.le,
        mul_le_mul_of_nonneg_right h2 (mul_nonneg hK.le (ha m))]
  have hk := key k0 hk0.1 le_rfl
  have hs := hN n hn k0
  have hlt : K * ∑ i ∈ Finset.Ico n k0, a i * b i < e ^ 2 := by
    have hKe : K * (e ^ 2 / K) = e ^ 2 := by field_simp
    calc K * ∑ i ∈ Finset.Ico n k0, a i * b i < K * (e ^ 2 / K) :=
          mul_lt_mul_of_pos_left hs hK
      _ = e ^ 2 := hKe
  nlinarith [mul_pos he0 (show 0 < b n - b k0 - e by linarith [hk0.2])]
