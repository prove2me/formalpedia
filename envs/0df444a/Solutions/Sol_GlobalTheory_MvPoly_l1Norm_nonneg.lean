-- Prove2me | solution 1 for GlobalTheory.MvPoly.l1Norm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:55:42.456348+00:00
-- url     : https://prove2.me/submissions/380ce1cc-6e44-4c18-8f45-fb7a8faf0670

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open GlobalTheory GlobalTheory.MvPoly
variable {σ τ K L : Type*}
variable [NormedCommRing K] [NormedCommRing L]
namespace GlobalTheory.MvPoly
theorem _root_.solution (P : MvPolynomial σ K) : 0 ≤ l1Norm P :=
  sum_nonneg fun _ _ ↦ norm_nonneg _
end GlobalTheory.MvPoly
