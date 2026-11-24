-- Prove2me | solution 1 for GlobalTheory.RealWeil.lineDeriv_mem_weylAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:54:04.085408+00:00
-- url     : https://prove2.me/submissions/6a09f914-733a-4e8f-9acc-37c9154f0787

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_dRho_mem_weylAlg
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
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (v : EuclideanSpace ℝ l) : lineDerivOpCLM ℂ (Sch l) v ∈ weylAlg l := by
  have : lineDerivOpCLM ℂ (Sch l) v = dRho (Sum.elim (fun i => v i) 0) := by
    ext f x
    have h1 : pPart (Sum.elim (fun i => v i) 0 : l ⊕ l → ℝ) = v := rfl
    have h2 : qPart (Sum.elim (fun i => v i) 0 : l ⊕ l → ℝ) = 0 := rfl
    simp [dRho_apply, h1, h2, lineDerivOp_apply_eq_fderiv]
  rw [this]; exact dRho_mem_weylAlg _
end GlobalTheory.RealWeil
