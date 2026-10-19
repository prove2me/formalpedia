-- Prove2me | solution 1 for GoodmanWitten.eq2_coherent_reduced_cross_section
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:50:30.102397+00:00
-- url     : https://prove2.me/submissions/87e248fd-785f-4171-b3a9-80a4e0388c61

import Mathlib
import Definitions.Def_GoodmanWitten_basic
open GoodmanWitten

theorem solution : ∃ C : ℝ, |C / 2.0e-35 - 1| ≤ 0.05 ∧
    ∀ A m Ybar Nbar : ℝ, 0 < A → 0 < m →
      reducedCrossSection A (coherentCrossSection m (nucleusMass A) Ybar Nbar) m =
        C * (4 * m * nucleusMass A / (m + nucleusMass A) ^ 2) * Ybar ^ 2 * (Nbar / 100) ^ 2 := by
  refine ⟨nucleonMass * fermiConstant ^ 2 * hbarc ^ 2 * 1e4 / (8 * Real.pi), ?_, ?_⟩
  · have p1 := Real.pi_gt_d6
    have p2 := Real.pi_lt_d6
    unfold nucleonMass fermiConstant hbarc
    rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ (by norm_num), le_div_iff₀ (by positivity)]; nlinarith
    · rw [sub_le_iff_le_add, div_le_iff₀ (by norm_num), div_le_iff₀ (by positivity)]; nlinarith
  · intro A m Ybar Nbar hA hm
    unfold reducedCrossSection coherentCrossSection elasticCrossSection coherentAmpSq nucleusMass
    have hpi := Real.pi_pos
    have hn : 0 < nucleonMass := by unfold nucleonMass; norm_num
    have : 0 < m + A * nucleonMass := by positivity
    field_simp
    ring
