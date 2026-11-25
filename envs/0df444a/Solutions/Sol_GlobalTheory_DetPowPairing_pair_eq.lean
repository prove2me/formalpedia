-- Prove2me | solution 1 for GlobalTheory.DetPowPairing.pair_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:02.930773+00:00
-- url     : https://prove2.me/submissions/4c87e47a-cdf5-46e1-b94a-654e4146bf84

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Theorems.Thm_GlobalTheory_DetPowPairing_pair_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
noncomputable section
open GlobalTheory GlobalTheory.DetPowPairing
open MvPolynomial
variable {σ : Type} {C : Type} [CommRing C]
namespace GlobalTheory.DetPowPairing
theorem _root_.solution (P Q : MvPolynomial σ C) :
    pair P Q = ∑ A ∈ P.support, coeff A P * wt C A * coeff A Q := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun A _ => pair_monomial A (coeff A P) Q
end GlobalTheory.DetPowPairing
