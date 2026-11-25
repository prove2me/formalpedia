-- Prove2me | solution 1 for GroundTheory.Automorphic.traceForm_neg_of_mem_skewPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:51.029798+00:00
-- url     : https://prove2.me/submissions/a491ece8-e74b-436f-8446-fa8f3a36c4f4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Theorems.Thm_GroundTheory_Automorphic_traceForm_apply
import Theorems.Thm_GroundTheory_Automorphic_re_trace_conjTranspose_mul_self_pos
import Theorems.Thm_GroundTheory_Automorphic_mem_skewPart

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
theorem _root_.solution {X : L} (hX : X ∈ skewPart L) (h0 : X ≠ 0) :
    traceForm L X X < 0 := by
  rw [mem_skewPart] at hX
  have hX0 : (X : Matrix ι ι 𝕜) ≠ 0 := fun e => h0 (Subtype.ext e)
  have e : (X : Matrix ι ι 𝕜) * X = -((X : Matrix ι ι 𝕜)ᴴ * X) := by
    rw [hX, Matrix.neg_mul, neg_neg]
  rw [traceForm_apply, e, trace_neg, map_neg, neg_lt_zero]
  exact re_trace_conjTranspose_mul_self_pos hX0
end GroundTheory.Automorphic
