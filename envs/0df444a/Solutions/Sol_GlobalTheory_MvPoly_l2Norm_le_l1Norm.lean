-- Prove2me | solution 1 for GlobalTheory.MvPoly.l2Norm_le_l1Norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:02:34.010252+00:00
-- url     : https://prove2.me/submissions/f0efd57b-a26f-484d-a4e1-ec9b2d770900

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_l1Norm_nonneg

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
theorem _root_.solution (P : MvPolynomial σ K) : l2Norm P ≤ l1Norm P :=
  Real.sqrt_le_iff.mpr ⟨l1Norm_nonneg P, sum_sq_le_sq_sum_of_nonneg fun _ _ ↦ norm_nonneg _⟩
end GlobalTheory.MvPoly
