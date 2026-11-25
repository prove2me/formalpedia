-- Prove2me | solution 1 for GlobalTheory.DetPairingBound.sum_eq_of_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:49:07.929606+00:00
-- url     : https://prove2.me/submissions/25e5027f-820b-4006-9aa6-ad52ff9cb64f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DeterminantPairingQuotientValuationLowerBound
import Theorems.Thm_GlobalTheory_DetPairingBound_cayDet_isHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.DetPairingBound
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
namespace GlobalTheory.DetPairingBound
theorem _root_.solution (C : Type) [CommRing C] (n x : ℕ) (A : Fin n × Fin n →₀ ℕ)
    (hA : A ∈ (cayDet n C ^ x).support) : ∑ j, A j = n * x := by
  have h := (cayDet_isHomogeneous n C).pow x
  rw [← Finsupp.degree_eq_sum]
  by_contra hne
  exact (mem_support_iff.mp hA) (h.coeff_eq_zero hne)
end GlobalTheory.DetPairingBound
