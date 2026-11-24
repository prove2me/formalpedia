-- Prove2me | solution 1 for GlobalTheory.KTypeSteps.sqrt_nsq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:29:46.534801+00:00
-- url     : https://prove2.me/submissions/e30c7144-59ed-4350-8b68-c0e2e51d227a

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_KtypesWithinSteps

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
theorem _root_.solution {n : ℕ} (v : Fin n → ℝ) :
    Real.sqrt (nsq v) = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [nsq, dot, sq]
end GlobalTheory.KTypeSteps
