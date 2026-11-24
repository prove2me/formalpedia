-- Prove2me | solution 1 for GlobalTheory.RealWeil.CoefQDecay.integral_prodTrans_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:55:14.459831+00:00
-- url     : https://prove2.me/submissions/0c9018ee-a086-4a7a-8b2d-ec1b674a9522

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPart
import Theorems.Thm_GlobalTheory_RealWeil_CoefQDecay_norm_iteratedFDeriv_prodTrans_le
import Theorems.Thm_GlobalTheory_RealWeil_CoefQDecay_integrable_derivBound
import Theorems.Thm_GlobalTheory_RealWeil_CoefQDecay_integrable_prodTrans

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
    ∫ x, ‖iteratedFDeriv ℝ j (prodTrans g g' p) x‖ ≤ ∫ x, derivBound g g' j x :=
  integral_mono (integrable_prodTrans g g' p j) (integrable_derivBound g g' j)
    (fun x => norm_iteratedFDeriv_prodTrans_le g g' p j x)
end GlobalTheory.RealWeil.CoefQDecay
