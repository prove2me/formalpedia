-- Prove2me | solution 1 for GlobalTheory.T.hermitian_norm_sq_le_re_mul_re_of_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:08:36.752379+00:00
-- url     : https://prove2.me/submissions/6e17512d-f2ed-4231-82fa-2eff759c3242

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HermitianFormNormSqLeReMulRe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HermitianFormNormSqLeReMulReStatement
import Theorems.Thm_GlobalTheory_hermitianForm_norm_sq_le_re_mul_re


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) → (∀ v, v ≠ 0 → 0 < (Bf v v).re) →
    ∀ v w, ‖Bf v w‖ ^ 2 ≤ (Bf v v).re * (Bf w w).re := by
  first | exact @GlobalTheory.hermitianForm_norm_sq_le_re_mul_re | exact GlobalTheory.hermitianForm_norm_sq_le_re_mul_re | (intros; apply GlobalTheory.hermitianForm_norm_sq_le_re_mul_re <;> assumption)
end _root_.GlobalTheory.T
