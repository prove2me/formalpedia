-- Prove2me | solution 1 for MNLBandit.UCB.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:32:51.216525+00:00
-- url     : https://prove2.me/submissions/766ca883-b5e5-412c-a05f-ca444ecef4be

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective

set_option autoImplicit false
open ChoiceCDLP.MNL

theorem solution {N : ℕ} (r : Fin N → ℝ) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (v u : Fin N → ℝ) (S : Finset (Fin N)) (hv : ∀ i ∈ S, 0 ≤ v i)
    (hvu : ∀ i ∈ S, v i ≤ u i) :
    mnlObjective u r 1 S - mnlObjective v r 1 S ≤
      (∑ j ∈ S, (u j - v j)) / (1 + ∑ j ∈ S, v j) := by
  unfold mnlObjective
  have hV : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg hv
  have hD : 0 ≤ ∑ j ∈ S, (u j - v j) := Finset.sum_nonneg (fun j hj => sub_nonneg.2 (hvu j hj))
  have ha : 0 ≤ ∑ j ∈ S, r j * v j :=
    Finset.sum_nonneg (fun j hj => mul_nonneg (hr j).1 (hv j hj))
  have hAa : ∑ j ∈ S, r j * u j - ∑ j ∈ S, r j * v j ≤ ∑ j ∈ S, (u j - v j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have := (hr j).1; have := (hr j).2; have := hvu j hj
    nlinarith
  have hU : ∑ j ∈ S, u j = ∑ j ∈ S, v j + ∑ j ∈ S, (u j - v j) := by
    rw [Finset.sum_sub_distrib]; ring
  set V := ∑ j ∈ S, v j
  set D := ∑ j ∈ S, (u j - v j)
  set a := ∑ j ∈ S, r j * v j
  set A := ∑ j ∈ S, r j * u j
  rw [hU]
  have h1 : 0 < V + D + 1 := by linarith
  have h2 : 0 < 1 + V := by linarith
  have h3 : 0 < 1 + (V + D) := by linarith
  have : A / (V + D + 1) - a / (V + 1) = ((A - a) * (V + 1) - a * D) / ((V + D + 1) * (V + 1)) := by
    field_simp
    ring
  rw [show V + 1 = 1 + V by ring] at this ⊢
  rw [this, div_le_div_iff₀ (by positivity) h2]
  have hh : 0 ≤ a * D := mul_nonneg ha hD
  have k1 : (A - a) * (V + 1) - a * D ≤ D * (V + D + 1) := by
    nlinarith [mul_nonneg hD hD, mul_le_mul_of_nonneg_right hAa (by linarith : (0:ℝ) ≤ V + 1)]
  have := mul_le_mul_of_nonneg_right k1 h2.le
  nlinarith [this]
