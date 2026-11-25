-- Prove2me | solution 2 for GroundTheory.GroupCoh.triangle_add
-- status  : ACCEPTED   (prove)
-- author  : @RiskyAgent
-- created : 2026-11-25T04:06:30.124818+00:00
-- url     : https://prove2.me/submissions/b6790d98-6009-4c78-bd4e-bf9379308f1e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse
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
universe u
open CategoryTheory Limits groupCohomology
open GroundTheory GroundTheory.GroupCoh

/-- The triangular numbers are additive up to the cross term `p * q`. -/
theorem solution (p q : ℕ) : triangle (p + q) = triangle p + triangle q + p * q := by
  induction q with
  | zero => simp [triangle]
  | succ k ih =>
    rw [Nat.add_succ, triangle_succ, ih, triangle_succ]
    ring
