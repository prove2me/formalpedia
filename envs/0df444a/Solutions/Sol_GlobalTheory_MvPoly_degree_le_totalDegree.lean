-- Prove2me | solution 1 for GlobalTheory.MvPoly.degree_le_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:45.08488+00:00
-- url     : https://prove2.me/submissions/db7a1701-5c4d-4564-9a16-548eeb5e86ab

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
variable [NormedCommRing K]
namespace GlobalTheory.MvPoly
theorem _root_.solution {R : Type*} [CommSemiring R] {P : MvPolynomial σ R} {α : σ →₀ ℕ}
    (h : α ∈ P.support) : α.degree ≤ P.totalDegree := le_totalDegree h
end GlobalTheory.MvPoly
