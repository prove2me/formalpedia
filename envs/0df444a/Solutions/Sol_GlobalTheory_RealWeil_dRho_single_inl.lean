-- Prove2me | solution 1 for GlobalTheory.RealWeil.dRho_single_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:41.438942+00:00
-- url     : https://prove2.me/submissions/0b6b668e-e697-41d3-81bb-91edf409c105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Theorems.Thm_GlobalTheory_RealWeil_dRho_apply

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
theorem _root_.solution (j : l) (f : Sch l) :
    dRho (Pi.single (Sum.inl j) 1) f = ∂_{(EuclideanSpace.single j 1 : EuclideanSpace ℝ l)} f := by
  have h1 : pPart (Pi.single (Sum.inl j) 1 : l ⊕ l → ℝ) = EuclideanSpace.single j 1 := by
    ext i
    simp [pPart, Pi.single_apply]
  have h2 : qPart (Pi.single (Sum.inl j) 1 : l ⊕ l → ℝ) = 0 := by
    ext i
    simp [qPart]
  ext x
  simp [dRho_apply, h1, h2, lineDerivOp_apply_eq_fderiv]
end GlobalTheory.RealWeil
