-- Prove2me | solution 1 for GlobalTheory.KTypeSteps.sqrt_nsq_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:45:00.786179+00:00
-- url     : https://prove2.me/submissions/8e9176ce-fc52-4c98-8c77-a6996b9fe230

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_KtypesWithinSteps
import Theorems.Thm_GlobalTheory_KTypeSteps_sqrt_nsq_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.KTypeSteps
namespace GlobalTheory.KTypeSteps
theorem _root_.solution {n : ℕ} (v w : Fin n → ℝ) :
    Real.sqrt (nsq (v + w)) ≤ Real.sqrt (nsq v) + Real.sqrt (nsq w) := by
  rw [sqrt_nsq_eq, sqrt_nsq_eq, sqrt_nsq_eq, WithLp.toLp_add]
  exact norm_add_le _ _
end GlobalTheory.KTypeSteps
