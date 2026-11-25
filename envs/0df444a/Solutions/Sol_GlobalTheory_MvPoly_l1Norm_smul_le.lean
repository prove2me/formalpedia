-- Prove2me | solution 1 for GlobalTheory.MvPoly.l1Norm_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:28.375568+00:00
-- url     : https://prove2.me/submissions/596812cb-44f7-4825-a660-3a487537c624

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
theorem _root_.solution (c : K) (P : MvPolynomial σ K) : l1Norm (c • P) ≤ ‖c‖ * l1Norm P := by
  rw [smul_eq_C_mul, ← l1Norm_C (σ := σ)]; exact l1Norm_mul_le _ _
end GlobalTheory.MvPoly
