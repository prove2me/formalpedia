-- Prove2me | solution 1 for InducedExpanderTest989.Structural.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T01:16:25.395542+00:00
-- url     : https://prove2.me/submissions/b92d88bd-396a-4945-843a-90c33ba5a5d4

import Definitions.Def_InducedExpanderTest989_Structural_Chains
set_option autoImplicit false
open scoped BigOperators
noncomputable section
open InducedExpanderTest989.Structural


theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (K : Matrix X X ℝ) (hK : Stochastic K) (a : X → ℝ) :
    tvNorm (Matrix.vecMul a K) ≤ tvNorm a := by
  have hrows := Matrix.mem_rowStochastic_iff_sum.mp hK
  unfold tvNorm MarkovChain.tvDist
  simp only [Pi.zero_apply, sub_zero, Matrix.vecMul, dotProduct]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    (∑ j, |∑ i, a i * K i j|) ≤ ∑ j, ∑ i, |a i * K i j| := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j, |a i * K i j| := Finset.sum_comm
    _ = ∑ i, ∑ j, |a i| * K i j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_mul, abs_of_nonneg (hrows.1 i j)]
    _ = ∑ i, |a i| := by
      simp_rw [← Finset.mul_sum, hrows.2, mul_one]



