-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.main
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-08T15:22:23.320992+00:00
-- url     : https://prove2.me/submissions/abe68b5e-4eb1-42ba-93ac-0208a6b95d5b

import Mathlib
import Definitions.Def_SidorenkoWeightedKernelData
import Theorems.Thm_OAI_SidorenkoCounterexample_weighted_kernel_strict_gap
import Theorems.Thm_OAI_SidorenkoCounterexample_weighted_kernel_sampling_defect

open scoped BigOperators
open OAI.SidorenkoCounterexample

/-- An explicit size bound makes the kernel gap larger than the sampling error. -/
private lemma sampling_error_below_gap {μ τ : ℝ} (hμ : 0 ≤ μ) (hgap : τ < μ ^ 66)
    {n : ℕ} (hn : 0 < n)
    (hsize : (595 + 66 * μ ^ 66) / (μ ^ 66 - τ) < n) :
    τ + 595 / (n : ℝ) < ((1 - 1 / (n : ℝ)) * μ) ^ 66 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hΔ : 0 < μ ^ 66 - τ := sub_pos.mpr hgap
  have hs := (div_lt_iff₀ hΔ).mp hsize
  have hd : (595 + 66 * μ ^ 66) / (n : ℝ) < μ ^ 66 - τ :=
    (div_lt_iff₀ hn').mpr (by nlinarith [hs])
  rw [add_div] at hd
  have hfirst : τ + 595 / (n : ℝ) < μ ^ 66 - 66 * μ ^ 66 / (n : ℝ) := by
    linarith
  apply hfirst.trans_le
  have hinv : 1 / (n : ℝ) ≤ 1 := (div_le_one hn').mpr hn1
  have hb := one_add_mul_le_pow (a := -(1 / (n : ℝ)))
    (by linarith : (-2 : ℝ) ≤ -(1 / (n : ℝ))) 66
  have hmul := mul_le_mul_of_nonneg_right hb (pow_nonneg hμ 66)
  calc
    _ = (1 + (66 : ℝ) * -(1 / (n : ℝ))) * μ ^ 66 := by ring
    _ ≤ (1 + -(1 / (n : ℝ))) ^ 66 * μ ^ 66 := hmul
    _ = _ := by rw [sub_eq_add_neg, mul_pow]

/-- A finite simple host with at least one edge violates Sidorenko's inequality. -/
theorem solution : ∃ size : ℕ, 0 < size ∧ ∃ host : SimpleGraph (Fin size),
    (∃ left right, host.Adj left right) ∧ homDensity H host < (edgeDensity host) ^ 66 := by
  classical
  obtain ⟨K, hμ, hgap⟩ := weighted_kernel_strict_gap
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max 0 ((595 + 66 * (kernelEdgeMean K) ^ 66) /
      ((kernelEdgeMean K) ^ 66 - kernelPatternMoment K)))
  have hnpos : 0 < n := by
    exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hn
  have hsize := lt_of_le_of_lt (le_max_right _ _) hn
  have hmean := sampling_error_below_gap hμ.le hgap hnpos hsize
  obtain ⟨m, w, hw, _htotal, G, havg⟩ := weighted_kernel_sampling_defect K n hnpos
  have havgneg :
      (∑ i, w i * (homDensity H (G i) - (edgeDensity (G i)) ^ 66)) < 0 :=
    havg.trans_lt (sub_neg.mpr hmean)
  have hex : ∃ i : Fin m, homDensity H (G i) < (edgeDensity (G i)) ^ 66 := by
    by_contra hc
    push_neg at hc
    have hnonneg :
        0 ≤ ∑ i, w i * (homDensity H (G i) - (edgeDensity (G i)) ^ 66) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sub_nonneg.mpr (hc i)))
    exact (not_lt_of_ge hnonneg) havgneg
  obtain ⟨i, hi⟩ := hex
  refine ⟨n, hnpos, G i, ?_, hi⟩
  by_contra hc
  push_neg at hc
  have hbot : G i = ⊥ := by
    apply SimpleGraph.ext
    funext a b
    apply propext
    simp only [SimpleGraph.bot_adj, iff_false]
    exact hc a b
  have he : edgeDensity (G i) = 0 := by
    simp [hbot, edgeDensity]
  have hnonneg : 0 ≤ homDensity H (G i) := by
    unfold homDensity
    positivity
  rw [he, zero_pow (by decide : 66 ≠ 0)] at hi
  exact (not_lt_of_ge hnonneg) hi

