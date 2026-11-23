-- Prove2me | solution 1 for GlobalTheory.RealWeil.pPart_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:52.661331+00:00
-- url     : https://prove2.me/submissions/bec46387-5962-4d54-b66b-1d88e811fa44

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
theorem _root_.solution (t : ℝ) (w : l ⊕ l → ℝ) : pPart (t • w) = t • pPart w := rfl
end GlobalTheory.RealWeil
