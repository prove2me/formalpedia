-- Prove2me | solution 1 for GlobalTheory.OddBlock.ExpShift.mixed_mul_X_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:12:39.8458+00:00
-- url     : https://prove2.me/submissions/2bb98cdc-0c4b-4ad9-9daf-b1c2711c5874

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
import Theorems.Thm_GlobalTheory_OddBlock_ExpShift_fact_add_single
import Theorems.Thm_GlobalTheory_OddBlock_ExpShift_pair_smul_right
import Theorems.Thm_GlobalTheory_OddBlock_ExpShift_slice_pderiv

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
    (g : MvPowerSeries (κ ⊕ κ') C) (j : κ') :
    mixed F (H * MvPolynomial.X (Sum.inr j)) g = mixed F H (MvPowerSeries.pderiv C (Sum.inr j) g) := by
  classical
  rw [mixed, mixed, form_mul_X]
  congr 2
  funext m
  have h1 : (Finsupp.sumFinsuppEquivProdFinsupp (m + Finsupp.single (Sum.inr j) 1)).1 =
      (Finsupp.sumFinsuppEquivProdFinsupp m).1 := by
    ext x; simp
  have h2 : (Finsupp.sumFinsuppEquivProdFinsupp (m + Finsupp.single (Sum.inr j) 1)).2 =
      (Finsupp.sumFinsuppEquivProdFinsupp m).2 + Finsupp.single j 1 := by
    ext x; simp [Finsupp.single_apply]
  rw [h1, h2, slice_pderiv, mul_smul_comm, pair_smul_right, fact_add_single, mul_assoc]
end GlobalTheory.OddBlock.ExpShift
