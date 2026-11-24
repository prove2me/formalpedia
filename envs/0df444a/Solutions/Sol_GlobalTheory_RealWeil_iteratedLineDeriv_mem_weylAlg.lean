-- Prove2me | solution 1 for GlobalTheory.RealWeil.iteratedLineDeriv_mem_weylAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:14:05.68874+00:00
-- url     : https://prove2.me/submissions/28918925-667e-4a58-8da5-8d25f2a74a11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_lineDeriv_mem_weylAlg

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
theorem _root_.solution {n : ℕ} (m : Fin n → EuclideanSpace ℝ l) :
    iteratedLineDerivOpCLM ℂ (Sch l) m ∈ weylAlg l := by
  induction n with
  | zero =>
    have : iteratedLineDerivOpCLM ℂ (Sch l) m = 1 := by
      ext1 f; simp
    rw [this]; exact one_mem _
  | succ n ih =>
    have : iteratedLineDerivOpCLM ℂ (Sch l) m =
        lineDerivOpCLM ℂ (Sch l) (m 0) * iteratedLineDerivOpCLM ℂ (Sch l) (Fin.tail m) := by
      ext1 f; simp [iteratedLineDerivOp_succ_left]
    rw [this]; exact mul_mem (lineDeriv_mem_weylAlg _) (ih _)
end GlobalTheory.RealWeil
