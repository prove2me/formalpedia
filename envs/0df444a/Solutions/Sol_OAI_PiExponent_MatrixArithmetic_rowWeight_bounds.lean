-- Prove2me | solution 1 for OAI.PiExponent.MatrixArithmetic.rowWeight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:47:24.418754+00:00
-- url     : https://prove2.me/submissions/6c3f0f4d-75d5-488b-84b9-291f0c32ab52

import Theorems.Thm_OAI_PiExponent_MatrixArithmetic_rowWeight_bounds_of_nonneg_weights
import Theorems.Thm_OAI_PiExponent_MatrixArithmetic_logWeights_nonneg
import Definitions.Def_PiExponent_FiniteMinorComparison

open OAI.PiExponent
open scoped BigOperators

theorem solution
    (m K : ℕ) (v0 theta H : ℝ) (q : Fin m → ℕ)
    (hK : 0 < K) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hH : 0 < H) (hq : ∀ i, 2 ≤ q i)
    (ρ : OAI.PiExponent.InterpolationMatrix.Row K v0 theta
      (OAI.PiExponent.MatrixArithmetic.logWeights q) H) :
    0 ≤ ∑ i : Fin m, (ρ.2.1 i.succ : ℝ) *
        OAI.PiExponent.MatrixArithmetic.logWeights q i ∧
      (∑ i : Fin m, (ρ.2.1 i.succ : ℝ) *
        OAI.PiExponent.MatrixArithmetic.logWeights q i) ≤ theta * H := by
  have hw : ∀ i, 0 ≤ OAI.PiExponent.MatrixArithmetic.logWeights q i :=
    OAI.PiExponent.MatrixArithmetic.logWeights_nonneg q hq
  exact OAI.PiExponent.MatrixArithmetic.rowWeight_bounds_of_nonneg_weights
    m K v0 theta H (OAI.PiExponent.MatrixArithmetic.logWeights q)
    hK hv0 htheta hH hw ρ
