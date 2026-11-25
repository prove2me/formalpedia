-- Prove2me | solution 1 for GlobalTheory.OddBlock.WindowValuationBound.val_neg_inv_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:07:37.347801+00:00
-- url     : https://prove2.me/submissions/e85f3c97-e4de-4706-b090-3199d92b730a

import Mathlib
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelliStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightNonnegExpOfWeightGeInvPrimeSubOneStatement
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FactorialWeightedPairingDetPowProportionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DeterminantPairingQuotientValuationLowerBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NewtonBoundPosAndNewtonStep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SumEqOfIsHomogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_exists_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.OddBlock GlobalTheory.OddBlock.WindowValuationBound
open Formalism.IncomingBounds (capNat LamP detL detR jetAt0 mvExp mfact hP expE PVar gam)
namespace GlobalTheory.OddBlock.WindowValuationBound
theorem _root_.solution {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {x : C} {r : ℝ}
    (h : v x = (r : WithTop ℝ)) : v (-x⁻¹) = ((-r : ℝ) : WithTop ℝ) := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [v.map_zero] at h
    exact WithTop.top_ne_coe h
  rw [v.map_neg]
  obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.exists_real v (inv_ne_zero hx)
  have e : v (x * x⁻¹) = 0 := by rw [mul_inv_cancel₀ hx, v.map_one]
  rw [v.map_mul, h, ht, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_inj] at e
  rw [ht]
  congr 1
  linarith
end GlobalTheory.OddBlock.WindowValuationBound
