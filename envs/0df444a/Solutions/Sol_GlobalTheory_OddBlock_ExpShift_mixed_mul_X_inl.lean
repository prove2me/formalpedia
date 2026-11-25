-- Prove2me | solution 1 for GlobalTheory.OddBlock.ExpShift.mixed_mul_X_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:23.599806+00:00
-- url     : https://prove2.me/submissions/2d8afa4f-9f4a-4d25-b8fd-f587254b87a4

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
import Theorems.Thm_GlobalTheory_OddBlock_ExpShift_form_mul_X
import Theorems.Thm_GlobalTheory_OddBlock_ExpShift_slice_X_inl_mul

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
theorem _root_.solution (F : MvPolynomial κ C) (H : MvPolynomial (κ ⊕ κ') C)
    (g : MvPowerSeries (κ ⊕ κ') C) (i : κ) :
    mixed F (H * MvPolynomial.X (Sum.inl i)) g = mixed F H (MvPowerSeries.X (Sum.inl i) * g) := by
  classical
  rw [mixed, mixed, form_mul_X]
  congr 2
  funext m
  have h1 : (Finsupp.sumFinsuppEquivProdFinsupp (m + Finsupp.single (Sum.inl i) 1)).1 =
      (Finsupp.sumFinsuppEquivProdFinsupp m).1 + Finsupp.single i 1 := by
    ext x; simp [Finsupp.single_apply]
  have h2 : (Finsupp.sumFinsuppEquivProdFinsupp (m + Finsupp.single (Sum.inl i) 1)).2 =
      (Finsupp.sumFinsuppEquivProdFinsupp m).2 := by
    ext x; simp
  rw [h1, h2, slice_X_inl_mul, ← mul_assoc, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial,
    mul_one]
end GlobalTheory.OddBlock.ExpShift
