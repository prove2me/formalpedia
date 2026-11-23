-- Prove2me | solution 1 for GlobalTheory.RealWeil.sympl_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:52.523177+00:00
-- url     : https://prove2.me/submissions/f2cc0eea-3e79-4660-afc9-01c41a46174d

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
variable [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (b : l ⊕ l) (u : l ⊕ l → ℝ) : sympl (Pi.single b 1) u = -(Matrix.J l ℝ *ᵥ u) b := by
  rcases b with b | b <;>
    simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, mulVec, dotProduct, Pi.single_apply, Matrix.one_apply]
end GlobalTheory.RealWeil
