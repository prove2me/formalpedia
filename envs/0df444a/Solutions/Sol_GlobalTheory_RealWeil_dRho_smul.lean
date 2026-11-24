-- Prove2me | solution 1 for GlobalTheory.RealWeil.dRho_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:52:57.973197+00:00
-- url     : https://prove2.me/submissions/2d8dcbe9-7476-4eaa-8460-e98f9898f82f

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
theorem _root_.solution (t : ℝ) (w : l ⊕ l → ℝ) : dRho (t • w) = (t : ℂ) • dRho w := by
  ext f x
  simp only [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, dRho_apply, pPart_smul, qPart_smul,
    real_inner_smul_left, map_smul, ofReal_mul, smul_eq_mul, real_smul]
  ring
end GlobalTheory.RealWeil
