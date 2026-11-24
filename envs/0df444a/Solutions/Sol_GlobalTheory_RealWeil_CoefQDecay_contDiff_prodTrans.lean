-- Prove2me | solution 1 for GlobalTheory.RealWeil.CoefQDecay.contDiff_prodTrans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:45.285402+00:00
-- url     : https://prove2.me/submissions/605756c1-7a1d-49b8-b0ed-105c86597f5d

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
theorem _root_.solution (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (prodTrans g g' p) := by
  have h1 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => g (x + p)) :=
    g.smooth'.comp (contDiff_id.add contDiff_const)
  have h2 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => starRingEnd ℂ (g' x)) :=
    Complex.conjCLE.contDiff.comp g'.smooth'
  exact h1.mul h2
end GlobalTheory.RealWeil.CoefQDecay
