-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.ConvergesAt.smul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T14:35:54.337932+00:00
-- url     : https://prove2.me/submissions/6343fd01-40f9-4576-ac21-15c182786397

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}

theorem solution (k : K) (ha : ConvergesAt a ρ) : ConvergesAt (k • a) ρ := by
  unfold ConvergesAt at *
  -- ‖k • a n‖ * ρ^n = ‖k‖ * (‖a n‖ * ρ^n) → ‖k‖ * 0 = 0
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  convert ha.mul_const ‖k‖ using 1
  · ext n; ring
  · rw [zero_mul]
