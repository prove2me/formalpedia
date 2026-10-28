-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualRowCount_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:06:40.541262+00:00
-- url     : https://prove2.me/submissions/a24cc78b-60d5-48a2-a436-ea22c3a217d7

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem solution {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) {H : Real} (hH : 0 < H) : 0 < (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) := by
  classical
  have hK : 1 ≤ d.K := d.K_pos
  have h0 : (fun _ => 0 : Fin (d.m + 1) → ℕ) ∈ OAI.PiExponent.strictWeightedSimplex
      (OAI.PiExponent.InterpolationMatrix.rowWeights (d.v0 : ℝ) (d.base.theta : ℝ)
        (MatrixArithmetic.logWeights (finiteDenominators d))) H := by
    simp only [OAI.PiExponent.strictWeightedSimplex, OAI.PiExponent.realWeightedSimplex,
      Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    simp [hH, hH.le]
  have : 0 < actualRowCount d H := by
    rw [actualRowCount, Fintype.card_pos_iff]
    exact ⟨(⟨0, by omega⟩, ⟨_, h0⟩)⟩
  exact_mod_cast this
