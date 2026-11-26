-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.single_zero_one_cmul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T14:37:12.86641+00:00
-- url     : https://prove2.me/submissions/66476601-130f-412a-b500-92d880cdfd3d

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

theorem solution (a : ℤ → K) : cmul (Pi.single 0 1) a = a := by
  ext n
  simp only [cmul]
  -- ∑' i, Pi.single 0 1 i * a (n-i) = a n, only i=0 survives
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro i hi
    simp [Pi.single_eq_of_ne hi]
