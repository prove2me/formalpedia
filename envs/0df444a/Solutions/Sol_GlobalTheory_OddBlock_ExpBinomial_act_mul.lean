-- Prove2me | solution 1 for GlobalTheory.OddBlock.ExpBinomial.act_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:02:20.947431+00:00
-- url     : https://prove2.me/submissions/b3b1f59c-c3d9-4483-a54f-34790cea8ea1

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
import Theorems.Thm_GlobalTheory_OddBlock_ExpBinomial_act_monomial

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
namespace GlobalTheory.OddBlock.ExpBinomial
theorem _root_.solution (g : MvPowerSeries (κ ⊕ κ') C) (R : MvPolynomial κ C)
    (P : MvPolynomial (κ ⊕ κ') C) :
    act g (MvPolynomial.rename Sum.inl R * P) = (R : MvPowerSeries κ C) * act g P := by
  induction R using MvPolynomial.induction_on' with
  | add p q hp hq => simp [add_mul, hp, hq]
  | monomial a c =>
    induction P using MvPolynomial.induction_on' with
    | add p q hp hq => simp only [mul_add, map_add, hp, hq]
    | monomial m d =>
      have h1 : (Finsupp.sumFinsuppEquivProdFinsupp (a.mapDomain Sum.inl + m)).1 =
          a + (Finsupp.sumFinsuppEquivProdFinsupp m).1 := by
        ext x
        simp [Finsupp.mapDomain_apply Sum.inl_injective]
      have h2 : (Finsupp.sumFinsuppEquivProdFinsupp (a.mapDomain Sum.inl + m)).2 =
          (Finsupp.sumFinsuppEquivProdFinsupp m).2 := by
        ext x
        simp [Finsupp.mapDomain_notin_range]
      rw [MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, act_monomial, act_monomial,
        actMon, actMon, h1, h2, MvPolynomial.coe_monomial]
      have h3 : (MvPowerSeries.monomial a c : MvPowerSeries κ C) =
          c • MvPowerSeries.monomial a (1 : C) := by
        rw [← map_smul]; simp
      have h4 : (MvPowerSeries.monomial (a + (Finsupp.sumFinsuppEquivProdFinsupp m).1) (1 : C)) =
          MvPowerSeries.monomial a (1 : C) *
            MvPowerSeries.monomial (Finsupp.sumFinsuppEquivProdFinsupp m).1 (1 : C) := by
        rw [MvPowerSeries.monomial_mul_monomial, one_mul]
      rw [h3, h4]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
      congr 1
      ring
end GlobalTheory.OddBlock.ExpBinomial
