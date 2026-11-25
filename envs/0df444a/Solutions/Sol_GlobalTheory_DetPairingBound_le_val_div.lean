-- Prove2me | solution 1 for GlobalTheory.DetPairingBound.le_val_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:54.242254+00:00
-- url     : https://prove2.me/submissions/3dcea64c-7272-4aa1-a78a-842290b42c9c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DeterminantPairingQuotientValuationLowerBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_div_eq_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_exists_real


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
theorem _root_.solution {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {N D : C} {a d r : ℝ}
    (hN : (a : WithTop ℝ) ≤ v N) (hD : v D = d) (h : r ≤ a - d) : (r : WithTop ℝ) ≤ v (N / D) := by
  have hD0 : D ≠ 0 := by
    rintro rfl
    simp at hD
  rcases eq_or_ne N 0 with rfl | hN0
  · simp
  · obtain ⟨b, hb⟩ := exists_real v hN0
    rw [div_eq_coe v hD0 hb hD]
    rw [hb, WithTop.coe_le_coe] at hN
    exact WithTop.coe_le_coe.mpr (by linarith)
end GlobalTheory.DetPairingBound
