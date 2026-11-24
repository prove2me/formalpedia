-- Prove2me | solution 1 for GlobalTheory.MvPoly.fockInner_monomial_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:00:48.733806+00:00
-- url     : https://prove2.me/submissions/2f5b1733-4f8b-4b7f-a1a3-216239ce9195

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
theorem _root_.solution (α : σ →₀ ℕ) (c : 𝕜) (Q : MvPolynomial σ 𝕜) :
    fockInner (monomial α c) Q = multiFactorial α * (c * starRingEnd 𝕜 (Q.coeff α)) := by
  classical
  rw [fockInner_eq_sum_of_subset_left Q (s := {α}) support_monomial_subset]
  simp
end GlobalTheory.MvPoly
