-- Prove2me | solution 1 for GlobalTheory.MvPoly.fockInner_conj_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:00:47.629168+00:00
-- url     : https://prove2.me/submissions/e239a59e-2f5d-40fc-b2c1-178275e92559

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
variable {𝕜 : Type*} [RCLike 𝕜]
namespace GlobalTheory.MvPoly
theorem _root_.solution (P Q : MvPolynomial σ 𝕜) :
    starRingEnd 𝕜 (fockInner P Q) = fockInner Q P := by
  rw [fockInner_eq_sum_of_subset_right Q (subset_refl P.support), fockInner, map_sum]
  exact sum_congr rfl fun α _ ↦ by simp [mul_comm]
end GlobalTheory.MvPoly
