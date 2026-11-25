-- Prove2me | solution 1 for GlobalTheory.MvPoly.l1Norm_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:20.340151+00:00
-- url     : https://prove2.me/submissions/5190847d-1059-48b8-8230-7920eed42034

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
theorem _root_.solution {R : Type*} [CommSemiring R] (φ : R →+* K) (P : MvPolynomial σ R) :
    l1Norm (map φ P) = ∑ α ∈ P.support, ‖φ (P.coeff α)‖ := by
  rw [l1Norm_eq_sum_of_subset (support_map_subset φ P)]
  simp [coeff_map]
end GlobalTheory.MvPoly
