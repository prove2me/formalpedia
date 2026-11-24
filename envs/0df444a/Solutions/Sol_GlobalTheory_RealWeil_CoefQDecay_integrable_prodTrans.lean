-- Prove2me | solution 1 for GlobalTheory.RealWeil.CoefQDecay.integrable_prodTrans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:12.267842+00:00
-- url     : https://prove2.me/submissions/5cc7def8-7dd2-4115-8e8e-bfa1372868a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPart
import Theorems.Thm_GlobalTheory_RealWeil_CoefQDecay_contDiff_prodTrans
import Theorems.Thm_GlobalTheory_RealWeil_CoefQDecay_norm_iteratedFDeriv_prodTrans_le
import Theorems.Thm_GlobalTheory_RealWeil_CoefQDecay_integrable_derivBound

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
theorem _root_.solution (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    Integrable (fun x => ‖iteratedFDeriv ℝ j (prodTrans g g' p) x‖) := by
  refine (integrable_derivBound g g' j).mono'
    ((contDiff_prodTrans g g' p).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_iteratedFDeriv_prodTrans_le g g' p j x
end GlobalTheory.RealWeil.CoefQDecay
