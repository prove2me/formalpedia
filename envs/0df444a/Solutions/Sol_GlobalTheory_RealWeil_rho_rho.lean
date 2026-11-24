-- Prove2me | solution 1 for GlobalTheory.RealWeil.rho_rho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:45.609422+00:00
-- url     : https://prove2.me/submissions/3e879869-6932-4c11-91ab-64c4f495589f

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
namespace GlobalTheory.RealWeil
theorem _root_.solution (w w' : l ⊕ l → ℝ) (f : L2 l) :
    rho w (rho w' f) = exp (((π * sympl w w' : ℝ) : ℂ) * I) • rho (w + w') f := rhoIsometry_rhoIsometry w w' f
end GlobalTheory.RealWeil
