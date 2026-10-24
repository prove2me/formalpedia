-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_row_count_pos
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:06:36.290502+00:00
-- url     : https://prove2.me/submissions/d05ce833-2e62-4234-9c0f-f18c7bf57292

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    {nu : Real} (d : FixedData nu) (H : Real) (hH : 0 < H) :
    0 < (actualRowCount d H : Real) := by
  classical
  let w := MatrixArithmetic.logWeights (finiteDenominators d)
  have hz :
      (fun _ : Fin (d.m + 1) => 0) ∈
        strictWeightedSimplex (InterpolationMatrix.rowWeights d.v0 d.base.theta w) H := by
    unfold strictWeightedSimplex
    apply Finset.mem_filter.mpr
    constructor
    · unfold realWeightedSimplex
      apply Finset.mem_filter.mpr
      constructor
      · simp
      · simpa using (le_of_lt hH)
    · simpa using hH
  have hrow : Nonempty (Row d H) := by
    refine ⟨(⟨0, ?_⟩, ⟨fun _ : Fin (d.m + 1) => 0, ?_⟩)⟩
    · exact Nat.lt_of_lt_of_le Nat.zero_lt_one d.K_pos
    · simpa [w] using hz
  unfold actualRowCount
  exact_mod_cast (Fintype.card_pos_iff.mpr hrow)