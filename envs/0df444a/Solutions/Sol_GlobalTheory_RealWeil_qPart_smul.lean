-- Prove2me | solution 1 for GlobalTheory.RealWeil.qPart_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:53.032234+00:00
-- url     : https://prove2.me/submissions/316c76da-e9ac-4af7-bf7b-3d0fa79cc4f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
omit [Fintype l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (t : ℝ) (w : l ⊕ l → ℝ) : qPart (t • w) = t • qPart w := rfl
end GlobalTheory.RealWeil
