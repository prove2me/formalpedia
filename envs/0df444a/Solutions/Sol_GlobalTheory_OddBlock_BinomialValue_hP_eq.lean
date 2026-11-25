-- Prove2me | solution 1 for GlobalTheory.OddBlock.BinomialValue.hP_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:08:17.717129+00:00
-- url     : https://prove2.me/submissions/0e1d3257-6cc3-4868-bd0e-bb40ff1ba3a7

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
theorem _root_.solution (l i n : ℕ) (h1 : MvPowerSeries (PVar n) C) :
    hP C l i n h1 = ((∑ q : Fin n × Fin n, MvPolynomial.C (-((l : C) ^ expE l i)⁻¹) *
      MvPolynomial.X (Sum.inl q) ^ (l ^ i) * MvPolynomial.X (Sum.inr q) : MvPolynomial (PVar n) C) :
        MvPowerSeries (PVar n) C) + h1 := by
  rw [hP, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum, Fintype.sum_prod_type, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_mul, MvPolynomial.coe_mul,
    MvPolynomial.coe_pow, MvPolynomial.coe_X, MvPolynomial.coe_X, MvPolynomial.coe_C, mul_assoc,
    MvPowerSeries.smul_eq_C_mul]
end GlobalTheory.OddBlock.BinomialValue
