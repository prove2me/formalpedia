-- Prove2me | solution 1 for NeymanPearsonClassification.binomial_lower_tail
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T17:40:26.825294+00:00
-- url     : https://prove2.me/submissions/e17bd662-912c-4d26-b5bf-251a1d6daa0e

import Mathlib
import Definitions.Def_NeymanPearsonClassification_Basic

open MeasureTheory ProbabilityTheory

namespace NeymanPearsonClassification

lemma bt_hoeff (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (L : ℝ) :
    (1 - q) + q * Real.exp (-L) ≤ Real.exp (-L * q + L ^ 2 / 8) := by
  set μ : Measure ℝ := ENNReal.ofReal (1 - q) • Measure.dirac 0 + ENNReal.ofReal q • Measure.dirac 1
    with hμ
  have : IsProbabilityMeasure μ := ⟨by
    simp only [hμ, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by linarith) hq0.le]; simp⟩
  have hint : ∀ f : ℝ → ℝ, ∫ x, f x ∂μ = (1 - q) * f 0 + q * f 1 := by
    intro f
    rw [hμ, integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
      integral_dirac, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hq0.le]
    · simp
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
  have hb : ∀ᵐ x ∂μ, (fun x : ℝ => x - q) x ∈ Set.Icc (-q) (1 - q) := by
    rw [hμ, ae_add_measure_iff]
    have hm : MeasurableSet {x : ℝ | x - q ∈ Set.Icc (-q) (1 - q)} :=
      measurableSet_Icc.preimage (measurable_id.sub_const q)
    constructor
    · exact Measure.ae_smul_measure ((ae_dirac_iff hm).2 (by simp)) _
    · exact Measure.ae_smul_measure ((ae_dirac_iff hm).2 (by simp)) _
  have hc : μ[fun x : ℝ => x - q] = 0 := by
    rw [hint]; ring
  have hs := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (measurable_id.sub_const q).aemeasurable hb hc
  have h := hs.mgf_le (-L)
  rw [mgf, hint] at h
  have hn : (‖(1 - q) - (-q)‖₊ : ℝ) = 1 := by
    rw [show (1 - q) - (-q) = (1 : ℝ) by ring]; simp
  rw [NNReal.coe_pow, NNReal.coe_div, hn] at h
  have e : Real.exp (-L * q + L ^ 2 / 8) = Real.exp (-L * q) * Real.exp ((1 / 2 : ℝ) ^ 2 * (-L) ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  have h2 : (1 - q) + q * Real.exp (-L) =
      Real.exp (-L * q) * ((1 - q) * Real.exp (-L * (0 - q)) + q * Real.exp (-L * (1 - q))) := by
    rw [mul_add, ← mul_assoc, mul_comm (Real.exp (-L * q)) (1 - q), mul_assoc, ← Real.exp_add,
      mul_left_comm, ← Real.exp_add]
    rw [show -L * q + -L * (0 - q) = 0 by ring, show -L * q + -L * (1 - q) = -L by ring]; simp
  rw [h2]
  gcongr
  refine (le_of_eq (by simp)).trans (h.trans (le_of_eq (by norm_num)))


end NeymanPearsonClassification

open NeymanPearsonClassification in
theorem solution (n : ℕ) (hn : 1 ≤ n) (q : ℝ) (hq : q ∈ Set.Ioo 0 1)
    (t : ℝ) (ht : 0 < t) (htq : t ≤ n * q / 2) :
    1 - Real.exp (-(n * q ^ 2 / 2)) ≤ binomTail n q t := by
  obtain ⟨hq0, hq1⟩ := hq
  set p : ℕ → ℝ := fun j => (n.choose j : ℝ) * q ^ j * (1 - q) ^ (n - j) with hp
  have hp0 : ∀ j, 0 ≤ p j := fun j => by
    simp only [hp]; have : 0 ≤ 1 - q := by linarith
    positivity
  have htot : ∑ j ∈ Finset.range (n + 1), p j = 1 := by
    have := add_pow q (1 - q) n
    rw [show q + (1 - q) = 1 by ring, one_pow] at this
    rw [this]; exact Finset.sum_congr rfl fun j _ => by simp only [hp]; ring
  set L : ℝ := 2 * q with hL
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1))
    (fun j : ℕ => t ≤ (j : ℝ)) p
  rw [htot] at hsplit
  have hlow : ∑ j ∈ (Finset.range (n + 1)).filter (fun j : ℕ => ¬ t ≤ (j : ℝ)), p j ≤
      ∑ j ∈ Finset.range (n + 1), p j * Real.exp (L * (t - j)) := by
    calc _ ≤ ∑ j ∈ (Finset.range (n + 1)).filter (fun j : ℕ => ¬ t ≤ (j : ℝ)), p j * Real.exp (L * (t - j)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          simp only [Finset.mem_filter, not_le] at hj
          have : 1 ≤ Real.exp (L * (t - j)) := Real.one_le_exp (by
            have : 0 < L := by positivity
            nlinarith)
          nlinarith [hp0 j]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j _ _ => mul_nonneg (hp0 j) (Real.exp_pos _).le)
  have hmgf : ∑ j ∈ Finset.range (n + 1), p j * Real.exp (L * (t - j)) =
      Real.exp (L * t) * (q * Real.exp (-L) + (1 - q)) ^ n := by
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hp]
    rw [mul_pow, ← Real.exp_nat_mul]
    rw [show L * (t - j) = L * t + j * -L by ring, Real.exp_add]
    ring
  have hH := bt_hoeff q hq0 hq1 L
  have hpow : (q * Real.exp (-L) + (1 - q)) ^ n ≤ Real.exp (-L * q + L ^ 2 / 8) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  rw [← Real.exp_nat_mul] at hpow
  have hfin : Real.exp (L * t) * Real.exp (n * (-L * q + L ^ 2 / 8)) ≤ Real.exp (-(n * q ^ 2 / 2)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    rw [hL]; nlinarith
  have : ∑ j ∈ (Finset.range (n + 1)).filter (fun j : ℕ => ¬ t ≤ (j : ℝ)), p j ≤ Real.exp (-(n * q ^ 2 / 2)) := by
    calc _ ≤ _ := hlow
      _ = _ := hmgf
      _ ≤ Real.exp (L * t) * Real.exp (n * (-L * q + L ^ 2 / 8)) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ ≤ _ := hfin
  unfold binomTail
  linarith
