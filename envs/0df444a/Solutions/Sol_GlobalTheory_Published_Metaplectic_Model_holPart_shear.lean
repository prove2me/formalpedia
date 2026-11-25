-- Prove2me | solution 1 for GlobalTheory.Published.Metaplectic.Model.holPart_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:09:16.617609+00:00
-- url     : https://prove2.me/submissions/4a13fd55-321f-475b-89e2-49cc9b69c9fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HolPartShear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.Metaplectic GlobalTheory.Published.Metaplectic.Model
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace GlobalTheory.Published.Metaplectic.Model
theorem _root_.solution (C : Matrix ι ι ℝ) (i : ι) : holPart (fromBlocks 1 0 C 1) i i = (2 + I * C i i) / 2 := by
  simp [holPart]; norm_num
end GlobalTheory.Published.Metaplectic.Model
