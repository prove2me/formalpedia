-- Prove2me | solution 1 for GlobalTheory.MvPoly.card_support_le_choose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:00:45.494933+00:00
-- url     : https://prove2.me/submissions/03ebf3ca-f96d-4f01-9158-b89f4aef720b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_support_subset_monomialsLE

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
variable [Fintype σ] [DecidableEq σ]
omit [DecidableEq σ]
namespace GlobalTheory.MvPoly
theorem _root_.solution {R : Type*} [CommSemiring R] {P : MvPolynomial σ R} {d : ℕ}
    (h : P.totalDegree ≤ d) : #P.support ≤ (Fintype.card σ + d).choose d := by
  classical
  exact card_monomialsLE σ d ▸ card_le_card (support_subset_monomialsLE.mpr h)
end GlobalTheory.MvPoly
