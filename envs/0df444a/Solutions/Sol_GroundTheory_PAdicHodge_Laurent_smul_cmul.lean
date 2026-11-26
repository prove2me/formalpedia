-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.smul_cmul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T14:34:19.312352+00:00
-- url     : https://prove2.me/submissions/ec096a5f-79c1-4589-b98a-bc522923cc5a

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
variable [CompleteSpace K]

theorem solution (k : K) (a b : ℤ → K) : cmul (k • a) b = k • cmul a b := by
  ext n
  simp only [cmul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  -- ∑' i, k * (a i * b (n-i)) = k * ∑' i, a i * b (n-i)
  exact tsum_mul_left
