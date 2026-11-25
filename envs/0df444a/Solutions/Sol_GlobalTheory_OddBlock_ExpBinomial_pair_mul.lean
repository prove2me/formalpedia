-- Prove2me | solution 1 for GlobalTheory.OddBlock.ExpBinomial.pair_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:08.732046+00:00
-- url     : https://prove2.me/submissions/95299eb0-4f4a-45cd-892f-c9729fe54b8a

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
import Theorems.Thm_GlobalTheory_OddBlock_ExpBinomial_pair_apply
import Theorems.Thm_GlobalTheory_OddBlock_ExpBinomial_coeff_homPart
import Theorems.Thm_GlobalTheory_OddBlock_ExpBinomial_sum_eq_of_isHomogeneous
import Theorems.Thm_GlobalTheory_BlockValue_Lead_prod
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_prod


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
open GlobalTheory GlobalTheory.OddBlock GlobalTheory.OddBlock.ExpBinomial
variable {C : Type} [Field C] {κ κ' : Type}
variable [Fintype κ] [DecidableEq κ]
namespace GlobalTheory.OddBlock.ExpBinomial
theorem _root_.solution {F R : MvPolynomial κ C} {d N : ℕ} (hF : F.IsHomogeneous (d + N))
    (hR : R.IsHomogeneous d) (S : MvPowerSeries κ C) :
    pair F ((R : MvPowerSeries κ C) * S) =
      ∑ A ∈ F.support, MvPolynomial.coeff A F * (A.prod fun _ e => (e.factorial : C)) *
        MvPolynomial.coeff A (R * homPart N S) := by
  rw [pair_apply]
  refine Finset.sum_congr rfl fun A hA => ?_
  congr 1
  have hA' := sum_eq_of_isHomogeneous hF (MvPolynomial.mem_support_iff.mp hA)
  rw [MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [MvPolynomial.coeff_coe]
  by_cases h : MvPolynomial.coeff x.1 R = 0
  · simp [h]
  · have h1 := sum_eq_of_isHomogeneous hR h
    have h2 : x.1 + x.2 = A := by simpa using hx
    rw [← h2] at hA'
    simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hA'
    rw [coeff_homPart, if_pos (by omega)]
end GlobalTheory.OddBlock.ExpBinomial
