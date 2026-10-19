-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualRowCount_eventually_at_least_one
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T02:35:34.218632+00:00
-- url     : https://prove2.me/submissions/9cc698a4-f06b-4504-b593-2433da9626c3

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped Topology

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    ∀ᶠ H : ℝ in atTop, 1 ≤ (actualRowCount d H : ℝ) := by
  classical
  filter_upwards [eventually_atTop.2 ⟨1, by
    intro H hH
    exact hH⟩] with H hH
  have hHpos : 0 < H := by linarith
  have hHnonneg : 0 ≤ H := le_of_lt hHpos
  let w : Fin (d.m + 1) → ℝ :=
    InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d))
  have hzero : (0 : Fin (d.m + 1) → ℕ) ∈ strictWeightedSimplex w H := by
    simp [strictWeightedSimplex, realWeightedSimplex, w, hHpos, hHnonneg]
  have hcard : 0 < actualRowCount d H := by
    rw [actualRowCount]
    apply Fintype.card_pos_iff.mpr
    refine ⟨⟨0, by have := d.K_pos; omega⟩, ⟨0, hzero⟩⟩
  exact_mod_cast (Nat.succ_le_of_lt hcard)