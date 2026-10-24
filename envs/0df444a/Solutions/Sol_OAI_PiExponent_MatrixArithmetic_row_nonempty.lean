-- Prove2me | solution 1 for OAI.PiExponent.MatrixArithmetic.row_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:52:12.322245+00:00
-- url     : https://prove2.me/submissions/f92dad40-272a-41bf-b5c3-d2dfc7d4f113

import Definitions.Def_PiExponent_FiniteMinorComparison

open OAI.PiExponent
open scoped BigOperators

theorem solution
    (m K : ℕ) (v0 theta H : ℝ) (q : Fin m → ℕ)
    (hK : 0 < K) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hH : 0 < H) (hq : ∀ i, 2 ≤ q i) :
    0 < Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 theta
      (OAI.PiExponent.MatrixArithmetic.logWeights q) H) := by
  classical
  let a : Fin (m + 1) → ℕ := fun _ => 0
  have ha : a ∈ OAI.PiExponent.strictWeightedSimplex
      (OAI.PiExponent.InterpolationMatrix.rowWeights v0 theta
        (OAI.PiExponent.MatrixArithmetic.logWeights q)) H := by
    rw [OAI.PiExponent.strictWeightedSimplex, Finset.mem_filter]
    constructor
    · rw [OAI.PiExponent.realWeightedSimplex, Finset.mem_filter]
      constructor
      · simp [a]
      · simp [a]
        linarith
    · simp [a]
      exact hH
  have hrow : Nonempty (OAI.PiExponent.InterpolationMatrix.Row K v0 theta
      (OAI.PiExponent.MatrixArithmetic.logWeights q) H) := by
    exact ⟨⟨⟨0, hK⟩, ⟨a, ha⟩⟩⟩
  exact Fintype.card_pos_iff.mpr hrow