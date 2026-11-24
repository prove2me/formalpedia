-- Prove2me | solution 1 for GlobalTheory.RealWeil.continuous_qPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:50:08.20099+00:00
-- url     : https://prove2.me/submissions/2c442122-f2f8-4da3-a720-26cf28924db7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousRhoApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
open scoped Matrix Real RealInnerProductSpace InnerProductSpace
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
omit [Fintype l]
namespace GlobalTheory.RealWeil
theorem _root_.solution : Continuous (qPart : (l ⊕ l → ℝ) → EuclideanSpace ℝ l) := by
  unfold qPart
  fun_prop
end GlobalTheory.RealWeil
