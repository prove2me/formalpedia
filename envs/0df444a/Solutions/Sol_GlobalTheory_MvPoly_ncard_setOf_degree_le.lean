-- Prove2me | solution 1 for GlobalTheory.MvPoly.ncard_setOf_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:02:37.652163+00:00
-- url     : https://prove2.me/submissions/b3bf19c5-94d1-4548-b24f-5d012fa93314

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
variable [Fintype σ] [DecidableEq σ]
omit [DecidableEq σ]
namespace GlobalTheory.MvPoly
theorem _root_.solution (d : ℕ) :
    {α : σ →₀ ℕ | α.degree ≤ d}.ncard = (Fintype.card σ + d).choose d := by
  classical
  rw [← card_monomialsLE, ← Set.ncard_coe_finset]
  congr 1
  ext α
  simp
end GlobalTheory.MvPoly
