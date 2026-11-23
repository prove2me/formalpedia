-- Prove2me | solution 1 for GlobalTheory.RealWeil.inner_toLp_rho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:30:13.168619+00:00
-- url     : https://prove2.me/submissions/4e71cbbe-1f0a-4114-b863-5d1ef8e2dd1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_coeFn_rho


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
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
omit [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (w : l ⊕ l → ℝ) (φ f : Sch l) :
    inner ℂ (φ.toLp 2 volume) (rho w (f.toLp 2 volume)) = ∫ x, inner ℂ (φ x) (rhoFun w f x) := by
  apply integral_congr_ae
  filter_upwards [φ.coeFn_toLp 2 volume, (coeFn_rho w (f.toLp 2 volume)).trans (rhoFun_congr w (f.coeFn_toLp 2 volume))]
    with x h1 h2
  rw [h1, h2]
end GlobalTheory.RealWeil
