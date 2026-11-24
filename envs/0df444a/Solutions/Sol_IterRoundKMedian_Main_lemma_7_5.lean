-- Prove2me | solution 1 for IterRoundKMedian.Main.lemma_7_5
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-23T23:32:42.305653+00:00
-- url     : https://prove2.me/submissions/b0a39681-19c4-48e3-acc2-dc4d5b2fb2d3

import Mathlib
import Definitions.Def_IterRoundKMedian_Main_ClientProfile

open IterRoundKMedian.Main.ClientProfile in
theorem solution {ι : Type*} [Fintype ι] (y d : ι → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hy1 : ∑ i, y i = 1) (hd : ∀ i, 0 ≤ d i) :
    A y d ≤ V y d + Real.sqrt (10 * Real.exp 1 * V y d * M y d)
      + 5 * Real.exp 1 / 2 * M y d := by
  classical
  have hVd : V y d = ∑ i, y i * d i := rfl
  have hMd : M y d = ∑ i, y i * |d i - V y d| := rfl
  set v := V y d with hv
  set μ := M y d with hμ
  have hV0 : 0 ≤ v := by rw [hVd]; exact Finset.sum_nonneg fun i _ => mul_nonneg (hy i) (hd i)
  have hM0 : 0 ≤ μ := by rw [hMd]; exact Finset.sum_nonneg fun i _ => mul_nonneg (hy i) (abs_nonneg _)
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hz : ∑ i, y i * (d i - v) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hy1, one_mul]
    linarith
  have hM2V : μ ≤ 2 * v := by
    have h : μ ≤ ∑ i, y i * (d i + v) := by
      rw [hMd]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (by rw [abs_le]; constructor <;> linarith [hd i]) (hy i)
    have h' : ∑ i, y i * (d i + v) = ∑ i, y i * (d i - v) + 2 * v * ∑ i, y i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hy1] at h'
    linarith
  have hpos : ∑ i, y i * max (d i - v) 0 = μ / 2 := by
    have h : ∀ i, y i * max (d i - v) 0 = (y i * |d i - v| + y i * (d i - v)) / 2 := by
      intro i
      rcases le_total 0 (d i - v) with h | h
      · rw [max_eq_left h, abs_of_nonneg h]; ring
      · rw [max_eq_right h, abs_of_nonpos h]; ring
    rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.sum_div, Finset.sum_add_distrib, hz, hMd]
    ring
  set t := Real.sqrt (5 * Real.exp 1 * v * μ / 2) with ht
  have hq : 0 ≤ 5 * Real.exp 1 * v * μ / 2 := by positivity
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htt : t * t = 5 * Real.exp 1 * v * μ / 2 := Real.mul_self_sqrt hq
  have hμt : μ ≤ t := by
    calc μ = Real.sqrt (μ ^ 2) := (Real.sqrt_sq hM0).symm
      _ ≤ t := Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left hM2V hM0, mul_nonneg hV0 hM0])
  have hS : ∑ i ∈ Finset.univ.filter (fun i => v + t < d i), y i * (d i - v) ≤ μ / 2 := by
    calc ∑ i ∈ Finset.univ.filter (fun i => v + t < d i), y i * (d i - v)
        ≤ ∑ i ∈ Finset.univ.filter (fun i => v + t < d i), y i * max (d i - v) 0 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hy i)
      _ ≤ ∑ i, y i * max (d i - v) 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => mul_nonneg (hy i) (le_max_right _ _))
      _ = μ / 2 := hpos
  have hY : t * ∑ i ∈ Finset.univ.filter (fun i => v + t < d i), y i ≤ μ / 2 := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun i hi => ?_) hS
    have h := (Finset.mem_filter.1 hi).2
    nlinarith [mul_nonneg (hy i) (sub_nonneg.2 h.le)]
  have hYkey : ∑ i ∈ Finset.univ.filter (fun i => v + t < d i), y i ≤ 1 / 2 ∧
      5 * Real.exp 1 * v * ∑ i ∈ Finset.univ.filter (fun i => v + t < d i), y i ≤ t := by
    rcases ht0.lt_or_eq with htp | htz
    · refine ⟨?_, ?_⟩
      · by_contra hc
        push_neg at hc
        nlinarith
      · have h5 : t * (5 * Real.exp 1 * v * ∑ i ∈ Finset.univ.filter (fun i => v + t < d i), y i)
            ≤ t * t := by
          rw [htt]
          have := mul_le_mul_of_nonneg_left hY (by positivity : (0:ℝ) ≤ 5 * Real.exp 1 * v)
          nlinarith
        exact le_of_mul_le_mul_left h5 htp
    · have hμ0 : μ = 0 := le_antisymm (htz ▸ hμt) hM0
      have hS0 : ∑ i ∈ Finset.univ.filter (fun i => v + t < d i), y i * (d i - v) = 0 := by
        apply le_antisymm (by linarith)
        exact Finset.sum_nonneg fun i hi => mul_nonneg (hy i)
          (by have := (Finset.mem_filter.1 hi).2; linarith)
      have hnn : ∀ i ∈ Finset.univ.filter (fun i => v + t < d i), 0 ≤ y i * (d i - v) :=
        fun i hi => mul_nonneg (hy i) (by have := (Finset.mem_filter.1 hi).2; linarith)
      have hY0 : ∑ i ∈ Finset.univ.filter (fun i => v + t < d i), y i = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hS0 i hi
        have hdi := (Finset.mem_filter.1 hi).2
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · exfalso; linarith
      rw [hY0]; constructor <;> [norm_num; (simp only [mul_zero]; exact ht0)]
  have hadm : Admissible y d (v + t) := by
    unfold Admissible
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => d i ≤ v + t) y
    simp only [not_le] at hsplit
    rw [hy1] at hsplit
    linarith [hYkey.1]
  have hT : T y d (v + t) =
      ∑ i ∈ Finset.univ.filter (fun i => v + t < d i), y i * (d i - v) +
        v * ∑ i ∈ Finset.univ.filter (fun i => v + t < d i), y i := by
    unfold T
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbdd : BddBelow ((fun R => R + 5 * Real.exp 1 * T y d R) '' {R | Admissible y d R}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨R, hR, rfl⟩
    have hR0 : 0 ≤ R := by
      by_contra hc
      push_neg at hc
      have hR' : (1 : ℝ) / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i => d i ≤ R), y i := hR
      have h0 : ∑ i ∈ Finset.univ.filter (fun i => d i ≤ R), y i = 0 :=
        Finset.sum_eq_zero fun i hi => absurd (Finset.mem_filter.1 hi).2 (by linarith [hd i])
      linarith
    have hT0 : 0 ≤ T y d R := Finset.sum_nonneg fun i _ => mul_nonneg (hy i) (hd i)
    show 0 ≤ R + 5 * Real.exp 1 * T y d R
    positivity
  have hA : A y d ≤ (v + t) + 5 * Real.exp 1 * T y d (v + t) :=
    csInf_le hbdd ⟨v + t, hadm, rfl⟩
  have h2t : Real.sqrt (10 * Real.exp 1 * v * μ) = 2 * t := by
    rw [show 10 * Real.exp 1 * v * μ = 2 ^ 2 * (5 * Real.exp 1 * v * μ / 2) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h2t]
  rw [hT] at hA
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith [hYkey.2, mul_le_mul_of_nonneg_left hS (by positivity : (0:ℝ) ≤ 5 * Real.exp 1)]
