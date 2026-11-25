-- Prove2me | solution 1 for GlobalTheory.OddBlock.BinomialValue.jetAt0_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:02:03.99586+00:00
-- url     : https://prove2.me/submissions/442ba13a-caff-4f91-8df7-a7cccd53a8bd

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
import Theorems.Thm_GlobalTheory_OddBlock_BinomialValue_mfact_cast
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
open Formalism.L2.FormalSeriesBounds
noncomputable section
open GlobalTheory GlobalTheory.OddBlock GlobalTheory.OddBlock.BinomialValue
open Formalism.IncomingBounds ReciprocityTheory.PGsh
variable {C : Type} [Field C]
namespace GlobalTheory.OddBlock.BinomialValue
theorem _root_.solution {σ τ : Type} (f : σ → τ) (hf : Function.Injective f) (P Q : MvPolynomial σ C) :
    jetAt0 (MvPolynomial.rename f P) ((MvPolynomial.rename f Q : MvPolynomial τ C) : MvPowerSeries τ C) =
      ∑ A ∈ P.support, MvPolynomial.coeff A P * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A Q := by
  classical
  rw [jetAt0, MvPolynomial.support_rename_of_injective hf,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective hf h]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_rename_mapDomain f hf, MvPolynomial.coeff_rename_mapDomain f hf,
    ← mfact_cast, Finsupp.prod_mapDomain_index_inj hf]
end GlobalTheory.OddBlock.BinomialValue
