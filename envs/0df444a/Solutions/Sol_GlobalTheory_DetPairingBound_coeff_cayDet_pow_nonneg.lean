-- Prove2me | solution 1 for GlobalTheory.DetPairingBound.coeff_cayDet_pow_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:41:54.115119+00:00
-- url     : https://prove2.me/submissions/812102fc-2711-43b4-8d93-0c1777a3cb99

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DeterminantPairingQuotientValuationLowerBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_intCast_nonneg
import Theorems.Thm_ReciprocityTheory_PGsh_cayDet_map


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
theorem _root_.solution (C : Type) [Field C] (v : AddValuation C (WithTop ℝ))
    (n x : ℕ) (A : Fin n × Fin n →₀ ℕ) : 0 ≤ v (coeff A (cayDet n C ^ x)) := by
  rw [← cayDet_map (R := C), ← map_pow, coeff_map, eq_intCast]
  exact intCast_nonneg v _
end GlobalTheory.DetPairingBound
