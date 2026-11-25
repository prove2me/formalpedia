-- Prove2me | solution 1 for GlobalTheory.OddBlock.WindowValuationBound.value_zero_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:53:18.266034+00:00
-- url     : https://prove2.me/submissions/1edb0fe9-7baf-4ce8-8979-cf5c91e98bd2

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
theorem _root_.solution (C : Type) [Field C] (l i : ℕ) (h1 : MvPowerSeries (PVar 0) C) (y : ℕ) :
    LamP C l i 0 h1 y = 1 := by
  have hL : detL C 0 = 1 := by simp [detL]
  have hR : detR C 0 = 1 := by simp [detR]
  unfold LamP jetAt0
  rw [hL, hR, one_pow, one_pow, one_mul, MvPolynomial.support_one, Finset.sum_singleton]
  have : MvPowerSeries.coeff (0 : PVar 0 →₀ ℕ) (mvExp (hP C l i 0 h1)) = 1 := by
    change ∑ k ∈ Finset.range ((0 : PVar 0 →₀ ℕ).degree + 1),
      MvPowerSeries.coeff 0 (hP C l i 0 h1 ^ k) / (k.factorial : C) = 1
    simp
  rw [this]
  simp [mfact]
end GlobalTheory.OddBlock.WindowValuationBound
