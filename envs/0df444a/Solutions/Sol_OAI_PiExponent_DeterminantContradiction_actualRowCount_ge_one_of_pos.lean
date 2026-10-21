-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualRowCount_ge_one_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:13:54.469597+00:00
-- url     : https://prove2.me/submissions/3b6c775b-713b-4a5d-8811-55b97e944dcf

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) (H : ℝ) (hH : 0 < H) : 1 ≤ actualRowCount d H := by
  classical
  have hK : 0 < d.K := lt_of_lt_of_le Nat.zero_lt_one d.K_pos
  have hmem : (fun _ : Fin (d.m + 1) => (0 : ℕ)) ∈
      strictWeightedSimplex
        (InterpolationMatrix.rowWeights (d.v0 : ℝ) (d.base.theta : ℝ)
          (MatrixArithmetic.logWeights (finiteDenominators d))) H := by
    rw [strictWeightedSimplex, Finset.mem_filter, realWeightedSimplex, Finset.mem_filter]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp
    · simp [hH.le]
    · simp [hH]
  have hne : Nonempty (Row d H) :=
    ⟨⟨⟨0, hK⟩, ⟨fun _ => 0, hmem⟩⟩⟩
  have hpos : 0 < Fintype.card (Row d H) := Fintype.card_pos_iff.mpr hne
  rw [actualRowCount]
  exact hpos
