-- Prove2me | solution 1 for GlobalTheory.RealWeil.dRho_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:32.728169+00:00
-- url     : https://prove2.me/submissions/2a90b64d-8c40-4f1a-bc92-f55024fe1a47

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
theorem _root_.solution (w : l ⊕ l → ℝ) (f : Sch l) (x : EuclideanSpace ℝ l) :
    dRho w f x = fderiv ℝ f x (pPart w) + 2 * π * I * (⟪qPart w, x⟫ : ℝ) * f x := by
  have h : (fun x : EuclideanSpace ℝ l => ((⟪qPart w, x⟫ : ℝ) : ℂ)).HasTemperateGrowth :=
    (ofRealCLM.comp (innerSL ℝ (qPart w))).hasTemperateGrowth
  simp [dRho, h, lineDerivOp_apply_eq_fderiv, mul_assoc]
end GlobalTheory.RealWeil
