-- Prove2me | solution 1 for GlobalTheory.OddBlock.ExpShift.pair_rename_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:28.948296+00:00
-- url     : https://prove2.me/submissions/09e96b34-37dd-4069-a21a-4c43392d26cb

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
import Theorems.Thm_GlobalTheory_OddBlock_ExpShift_form_rename
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
theorem _root_.solution (F : MvPolynomial κ C) (g : MvPowerSeries (κ ⊕ κ') C) :
    pair (MvPolynomial.rename Sum.inl F) g = pair F (slice 0 g) := by
  rw [pair, pair, form_rename]
  congr 2
  funext A
  have h : A.mapDomain Sum.inl = Finsupp.sumFinsuppEquivProdFinsupp.symm (A, (0 : κ' →₀ ℕ)) := by
    ext x
    rcases x with x | x
    · rw [Finsupp.mapDomain_apply Sum.inl_injective]; simp
    · rw [Finsupp.mapDomain_notin_range _ _ (by simp)]; simp
  rw [coeff_slice, ← h, fact, fact, Finsupp.prod_mapDomain_index_inj Sum.inl_injective]
end GlobalTheory.OddBlock.ExpShift
