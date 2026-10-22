-- Prove2me | solution 1 for LeviBalancing.DualBalancing.backlog_on_TPi_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:31:19.942995+00:00
-- url     : https://prove2.me/submissions/5a47bfa1-7a9c-433d-bb30-29d2cad21545

import Mathlib
import Definitions.Def_LeviBalancing_DualBalancing_Model
open Finset


namespace LeviBalancing.DualBalancing

theorem backlog_core (I : Instance) (d : ℤ → ℝ)
    (hd : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ d t) (qB qP : ℤ → ℝ)
    (hqB : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ qB t)
    (hqP : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ qP t) :
    ∑ t ∈ (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter
        (fun t => invPositionAfter I d qP t ≤ invPositionAfter I d qB t),
        marginalBacklog I d qB t ≤
      ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), marginalBacklog I d qP t := by
  have hp : ∀ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), 0 ≤ I.p (t + I.L) := by
    intro t ht
    rw [mem_Icc] at ht
    exact I.p_nonneg _ (by omega) (by omega)
  calc ∑ t ∈ (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter
        (fun t => invPositionAfter I d qP t ≤ invPositionAfter I d qB t),
        marginalBacklog I d qB t
      ≤ ∑ t ∈ (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter
        (fun t => invPositionAfter I d qP t ≤ invPositionAfter I d qB t),
        marginalBacklog I d qP t := by
        apply sum_le_sum
        intro t ht
        rw [mem_filter] at ht
        unfold marginalBacklog
        apply mul_le_mul_of_nonneg_left _ (hp t ht.1)
        exact max_le_max (by linarith [ht.2]) le_rfl
    _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro t ht _
        unfold marginalBacklog
        exact mul_nonneg (hp t ht) (le_max_right _ _)

end LeviBalancing.DualBalancing

open LeviBalancing.DualBalancing


theorem solution (I : Instance) (d : ℤ → ℝ)
    (hd : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ d t) (qB qP : ℤ → ℝ)
    (hqB : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ qB t)
    (hqP : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ qP t) :
    ∑ t ∈ (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter
        (fun t => invPositionAfter I d qP t ≤ invPositionAfter I d qB t),
        marginalBacklog I d qB t ≤
      ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), marginalBacklog I d qP t := by
  exact backlog_core I d hd qB qP hqB hqP
