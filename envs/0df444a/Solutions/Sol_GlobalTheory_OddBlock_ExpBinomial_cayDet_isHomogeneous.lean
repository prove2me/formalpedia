-- Prove2me | solution 1 for GlobalTheory.OddBlock.ExpBinomial.cayDet_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:09:05.26843+00:00
-- url     : https://prove2.me/submissions/38bf06b7-780f-408e-a320-abaf25f6e198

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
import Theorems.Thm_GlobalTheory_BlockValue_Lead_prod
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_prod
import Theorems.Thm_GlobalTheory_DetPowDegree_Good_neg


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
namespace GlobalTheory.OddBlock.ExpBinomial
theorem _root_.solution (n : ℕ) (C : Type) [CommRing C] : (cayDet n C).IsHomogeneous n := by
  rw [cayDet, Matrix.det_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun g _ => ?_
  have h : (∏ i, (MvPolynomial.X (g i, i) : MvPolynomial (Fin n × Fin n) C)).IsHomogeneous n := by
    have := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n))
      (fun i => (MvPolynomial.X (g i, i) : MvPolynomial (Fin n × Fin n) C)) (fun _ => 1)
      (fun i _ => MvPolynomial.isHomogeneous_X _ _)
    simpa using this
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with e | e
  · simpa [e] using h
  · simpa [e] using h.neg
end GlobalTheory.OddBlock.ExpBinomial
