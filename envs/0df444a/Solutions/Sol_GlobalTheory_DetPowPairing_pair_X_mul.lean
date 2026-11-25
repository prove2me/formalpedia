-- Prove2me | solution 1 for GlobalTheory.DetPowPairing.pair_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:47.02842+00:00
-- url     : https://prove2.me/submissions/25cc849d-8f25-470b-a065-5044eb28649c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Theorems.Thm_GlobalTheory_DetPowPairing_pair_monomial
import Theorems.Thm_GlobalTheory_DetPowPairing_pair_eq
import Theorems.Thm_GlobalTheory_DetPowPairing_wt_add_single
import Theorems.Thm_P2M_GlobalTheory_DetPowPairing_coeff_pderiv__dbf7971f6bc0

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
theorem _root_.solution (j : σ) (P Q : MvPolynomial σ C) :
    pair (P * X j) Q = pair P (pderiv j Q) := by
  conv_lhs => rw [P.as_sum]
  rw [pair_eq P, Finset.sum_mul, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [show (X j : MvPolynomial σ C) = monomial (Finsupp.single j 1) 1 from rfl, monomial_mul, mul_one,
    pair_monomial, coeff_pderiv', wt_add_single]
  ring
end GlobalTheory.DetPowPairing
