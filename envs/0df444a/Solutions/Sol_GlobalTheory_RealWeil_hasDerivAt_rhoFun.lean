-- Prove2me | solution 1 for GlobalTheory.RealWeil.hasDerivAt_rhoFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:50:09.905127+00:00
-- url     : https://prove2.me/submissions/90df257e-3b6d-4cf9-957d-50df4927eeb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Theorems.Thm_GlobalTheory_RealWeil_pPart_smul
import Theorems.Thm_GlobalTheory_RealWeil_qPart_smul
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
namespace GlobalTheory.RealWeil
theorem _root_.solution (w : l ⊕ l → ℝ) (f : Sch l) (x : EuclideanSpace ℝ l) :
    HasDerivAt (fun t : ℝ => rhoFun (t • w) f x) (dRho w f x) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * π * (t * ⟪qPart w, x⟫) + π * (t * (t * ⟪pPart w, qPart w⟫)))
      (2 * π * ⟪qPart w, x⟫) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const ⟪qPart w, x⟫).const_mul (2 * π)).add
      (((hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_id (0 : ℝ)).mul_const ⟪pPart w, qPart w⟫)).const_mul π)
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.mul_const I).cexp
  have h3 : HasDerivAt (fun t : ℝ => x + t • pPart w) (pPart w) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (pPart w)).const_add x
  have h4 : HasDerivAt (fun t : ℝ => f (x + t • pPart w)) (fderiv ℝ f x (pPart w)) 0 := by
    have := (f.hasFDerivAt (x + (0 : ℝ) • pPart w)).comp_hasDerivAt (0 : ℝ) h3
    simpa [Function.comp_def] using this
  have h5 := h2.mul h4
  refine (h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => ?_)
  · rw [dRho_apply]
    simp
    ring
  · simp only [rhoFun, phase, pPart_smul, qPart_smul, real_inner_smul_left, real_inner_smul_right, Pi.mul_apply]
end GlobalTheory.RealWeil
