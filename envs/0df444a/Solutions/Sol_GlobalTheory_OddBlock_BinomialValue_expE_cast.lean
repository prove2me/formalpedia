-- Prove2me | solution 1 for GlobalTheory.OddBlock.BinomialValue.expE_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:52:09.628812+00:00
-- url     : https://prove2.me/submissions/0edb4c78-f94b-4802-84d4-e2a11d9533ef

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
theorem _root_.solution {l i : ℕ} (hl : 2 ≤ l) (hi : Odd i) :
    (expE l i : ℝ) = 1 + ((l : ℝ) ^ i - l) / ((l : ℝ) ^ 2 - 1) := by
  have h1 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h3 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  obtain ⟨k, rfl⟩ := hi
  have hk : (2 * k + 1 - 1) / 2 = k := by omega
  have hne : (l : ℝ) ^ 2 ≠ 1 := fun h => h3 (by rw [h]; ring)
  unfold expE
  rw [hk]
  push_cast
  rw [geom_sum_eq hne, ← pow_mul]
  field_simp
  ring
end GlobalTheory.OddBlock.BinomialValue
