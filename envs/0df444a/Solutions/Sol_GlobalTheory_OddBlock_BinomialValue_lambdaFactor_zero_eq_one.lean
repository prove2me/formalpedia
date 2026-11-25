-- Prove2me | solution 1 for GlobalTheory.OddBlock.BinomialValue.lambdaFactor_zero_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:52:11.734798+00:00
-- url     : https://prove2.me/submissions/96b06681-19f8-4609-bf79-1d08379cce84

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
noncomputable section
open GlobalTheory GlobalTheory.OddBlock GlobalTheory.OddBlock.BinomialValue
open Formalism.IncomingBounds ReciprocityTheory.PGsh
variable {C : Type} [Field C]
namespace GlobalTheory.OddBlock.BinomialValue
theorem _root_.solution [CharZero C] (l i : ℕ) (h1 : MvPowerSeries (PVar 0) C) (y : ℕ) : LamP C l i 0 h1 y = 1 := by
  have hL : detL C 0 = 1 := Matrix.det_isEmpty
  have hR : detR C 0 = 1 := Matrix.det_isEmpty
  rw [LamP, hL, hR, one_pow, one_pow, one_mul, jetAt0, MvPolynomial.support_one, Finset.sum_singleton]
  have : MvPowerSeries.coeff 0 (mvExp (hP C l i 0 h1)) = 1 := by
    show (∑ k ∈ Finset.range ((0 : PVar 0 →₀ ℕ).degree + 1), MvPowerSeries.coeff 0 (hP C l i 0 h1 ^ k) / (k.factorial : C)) = 1
    simp
  rw [this]
  simp [mfact]
end GlobalTheory.OddBlock.BinomialValue
