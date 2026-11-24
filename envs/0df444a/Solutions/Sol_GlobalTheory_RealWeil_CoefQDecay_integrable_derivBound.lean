-- Prove2me | solution 1 for GlobalTheory.RealWeil.CoefQDecay.integrable_derivBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:45.381747+00:00
-- url     : https://prove2.me/submissions/dc6eb3c8-d729-48ac-9ada-dda6316e3ffb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
open scoped FourierTransform ContDiff RealInnerProductSpace Real
noncomputable section
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.CoefQDecay
variable {n : ℕ}
namespace GlobalTheory.RealWeil.CoefQDecay
theorem _root_.solution (g g' : Sch (Fin n)) (j : ℕ) : Integrable (derivBound g g' j) := by
  unfold derivBound
  refine integrable_finset_sum _ fun i _ => ?_
  have := SchwartzMap.integrable_pow_mul_iteratedFDeriv volume g' 0 (j - i)
  simp only [pow_zero, one_mul] at this
  exact this.const_mul _
end GlobalTheory.RealWeil.CoefQDecay
