-- Prove2me | solution 1 for LevyStochCalc.Ito.JumpSplitting.tendsto_nhdsLT_sum_filter_le
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T18:28:11.957529+00:00
-- url     : https://prove2.me/submissions/15dbcf96-715f-4859-b798-431ebad5a85c

import Mathlib

set_option autoImplicit false

open Filter
open scoped Topology

theorem solution {K : ℕ} (θ : Fin K → ℝ) (c : Fin K → ℝ) (b : ℝ) :
    Tendsto (fun t => ∑ j ∈ Finset.univ.filter fun j => θ j ≤ t, c j)
      (𝓝[<] b) (𝓝 (∑ j ∈ Finset.univ.filter fun j => θ j < b, c j)) := by
  simp only [Finset.sum_filter]
  apply tendsto_finset_sum
  intro j _
  by_cases hθ : θ j < b
  · have hevent : ∀ᶠ t in 𝓝[<] b, θ j < t :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hθ)
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with t ht
    simp only [if_pos hθ, if_pos ht.le]
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hnot : ¬ θ j ≤ t := not_le.mpr (ht.trans_le (le_of_not_gt hθ))
    simp only [if_neg hθ, if_neg hnot]

#print axioms solution
