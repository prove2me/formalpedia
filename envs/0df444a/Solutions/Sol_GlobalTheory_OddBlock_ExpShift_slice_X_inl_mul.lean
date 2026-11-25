-- Prove2me | solution 1 for GlobalTheory.OddBlock.ExpShift.slice_X_inl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:01:36.90041+00:00
-- url     : https://prove2.me/submissions/27965599-e59c-48dd-be54-b56acaa648fa

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
import Theorems.Thm_GlobalTheory_OddBlock_ExpShift_coeff_slice

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
open GlobalTheory GlobalTheory.OddBlock GlobalTheory.OddBlock.ExpShift
variable {C : Type} [Field C] {κ κ' : Type}
namespace GlobalTheory.OddBlock.ExpShift
theorem _root_.solution (b : κ' →₀ ℕ) (g : MvPowerSeries (κ ⊕ κ') C) (i : κ) :
    slice b (MvPowerSeries.X (Sum.inl i) * g) = MvPowerSeries.X i * slice b g := by
  classical
  ext A
  have h : Finsupp.sumFinsuppEquivProdFinsupp.symm (A, b) - Finsupp.single (Sum.inl i) 1 =
      Finsupp.sumFinsuppEquivProdFinsupp.symm (A - Finsupp.single i 1, b) := by
    ext x
    rcases x with x | x <;> simp [Finsupp.single_apply]
  rw [coeff_slice, MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul,
    MvPowerSeries.coeff_monomial_mul, h, coeff_slice]
  simp [Finsupp.single_le_iff]
end GlobalTheory.OddBlock.ExpShift
