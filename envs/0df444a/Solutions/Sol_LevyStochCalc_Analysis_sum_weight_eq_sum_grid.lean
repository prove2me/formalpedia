-- Prove2me | solution 1 for LevyStochCalc.Analysis.sum_weight_eq_sum_grid
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:26:13.204249+00:00
-- url     : https://prove2.me/submissions/b5e642a8-26da-4929-bc7c-70c722e78e58

import Definitions.Def_LevyStochCalc_Analysis_SortedGrid_F000

namespace LevyStochCalc.Analysis

open Finset

variable (S : Finset ℝ)

variable {d : ℕ} {T : ℝ}

theorem _root_.solution (F : Finset (Fin d × Set.Iic T)) (w : F → ℝ)
    (v : Fin d → ℝ → ℝ) (hv : ∀ p : F, (p.1.2 : ℝ) ≤ 0 → v p.1.1 (p.1.2 : ℝ) = 0)
    {S : Finset ℝ} (hS : posTimes F ⊆ S) (hSpos : ∀ x ∈ S, 0 < x) :
    ∑ p : F, v p.1.1 (p.1.2 : ℝ) * w p
      = ∑ i, ∑ k ∈ Finset.Ico 1 (S.card + 1),
          weightAt F w (sortedGrid S k) i * v i (sortedGrid S k) := by
  refine Eq.trans ?_ (Finset.sum_comm.trans
    (sum_Ico_sortedGrid S (fun x => ∑ i, weightAt F w x i * v i x))).symm
  simp_rw [sum_weightAt_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact mul_comm _ _
  · have hle : (p.1.2 : ℝ) ≤ 0 := by
      by_contra hc
      exact h (hS (mem_posTimes p.2 (lt_of_not_ge hc)))
    rw [hv p hle, zero_mul]

end LevyStochCalc.Analysis
