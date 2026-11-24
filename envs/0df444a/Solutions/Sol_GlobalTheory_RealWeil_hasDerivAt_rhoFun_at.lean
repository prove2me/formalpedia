-- Prove2me | solution 1 for GlobalTheory.RealWeil.hasDerivAt_rhoFun_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:11:39.3128+00:00
-- url     : https://prove2.me/submissions/2bec86d1-bf71-4117-bc4e-41c7bf0f3fe7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_hasDerivAt_rhoFun
import Theorems.Thm_GlobalTheory_RealWeil_pPart_smul
import Theorems.Thm_GlobalTheory_RealWeil_qPart_smul


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
theorem _root_.solution (w : l ⊕ l → ℝ) (f : Sch l) (x : EuclideanSpace ℝ l) (t : ℝ) :
    HasDerivAt (fun t : ℝ => rhoFun (t • w) f x) (rhoFun (t • w) (dRho w f) x) t := by
  have h1 := ((hasDerivAt_rhoFun w f (x + pPart (t • w))).const_mul (phase (t • w) x))
  have h2 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h3 := HasDerivAt.scomp_of_eq (𝕜 := ℝ) (𝕜' := ℝ) t h1 h2 (by simp)
  rw [one_smul] at h3
  refine h3.congr_of_eventuallyEq (.of_forall fun s => ?_)
  have h4 := congrFun (rhoFun_rhoFun (t • w) ((s - t) • w) f) x
  have h5 : sympl (t • w) ((s - t) • w) = 0 := by
    simp only [sympl, pPart_smul, qPart_smul, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (pPart w) (qPart w)]
    ring
  rw [h5, ← add_smul, add_sub_cancel] at h4
  simpa [rhoFun] using h4.symm
end GlobalTheory.RealWeil
