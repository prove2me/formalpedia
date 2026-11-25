-- Prove2me | solution 1 for GroundTheory.Automorphic.traceForm_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:34:42.923802+00:00
-- url     : https://prove2.me/submissions/3067476e-50bd-42c2-b06e-1f763ee8b294

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Theorems.Thm_GroundTheory_Automorphic_traceForm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (L : LieSubalgebra ℝ (Matrix ι ι 𝕜))
variable {L}
namespace GroundTheory.Automorphic
theorem _root_.solution (X Y : L) : traceForm L X Y = traceForm L Y X := by
  rw [traceForm_apply, traceForm_apply, trace_mul_comm]
end GroundTheory.Automorphic
