-- Prove2me | solution 1 for GroundTheory.Automorphic.traceForm_pos_of_mem_hermPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:41:56.646831+00:00
-- url     : https://prove2.me/submissions/cf220bc7-155c-4db2-b6d2-5417febb0167

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Theorems.Thm_GroundTheory_Automorphic_traceForm_apply
import Theorems.Thm_GroundTheory_Automorphic_re_trace_conjTranspose_mul_self_pos
import Theorems.Thm_GroundTheory_Automorphic_mem_hermPart

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
theorem _root_.solution {X : L} (hX : X ∈ hermPart L) (h0 : X ≠ 0) :
    0 < traceForm L X X := by
  rw [mem_hermPart] at hX
  have hX0 : (X : Matrix ι ι 𝕜) ≠ 0 := fun e => h0 (Subtype.ext e)
  rw [traceForm_apply]
  nth_rewrite 1 [← hX]
  exact re_trace_conjTranspose_mul_self_pos hX0
end GroundTheory.Automorphic
