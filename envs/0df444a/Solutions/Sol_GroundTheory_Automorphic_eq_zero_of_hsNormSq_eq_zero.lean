-- Prove2me | solution 1 for GroundTheory.Automorphic.eq_zero_of_hsNormSq_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:14:02.584999+00:00
-- url     : https://prove2.me/submissions/0fd2db5f-9132-436d-bdc1-432b20d71a44

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Definitions.Def_GroundTheory_AutomorphicForms_TraceNormComp
import Theorems.Thm_GroundTheory_Automorphic_enorm_apply_sq_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace GroundTheory.Automorphic
theorem _root_.solution {T : H →L[ℂ] H} (h : hsNormSq T = 0) : T = 0 := by
  ext x
  have hx := enorm_apply_sq_le T x
  rw [h, zero_mul, nonpos_iff_eq_zero, pow_eq_zero_iff two_ne_zero, enorm_eq_zero] at hx
  simpa using hx
end GroundTheory.Automorphic
