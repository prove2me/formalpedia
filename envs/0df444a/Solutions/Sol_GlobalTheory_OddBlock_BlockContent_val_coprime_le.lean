-- Prove2me | solution 1 for GlobalTheory.OddBlock.BlockContent.val_coprime_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:02:08.746803+00:00
-- url     : https://prove2.me/submissions/54ff26de-c5e9-4e75-b4a0-37d5d23901b0

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
import Theorems.Thm_GlobalTheory_OddBlock_BlockContent_val_intCast_nonneg
import Theorems.Thm_GlobalTheory_RadiiIdentities_val_intCast_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open GlobalTheory GlobalTheory.OddBlock GlobalTheory.OddBlock.BlockContent
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
namespace GlobalTheory.OddBlock.BlockContent
theorem _root_.solution {l m : ℕ} (hv : v (l : C) = 1) (h : Nat.Coprime l m) : v (m : C) ≤ 0 := by
  by_contra hm
  push_neg at hm
  have hb : (1 : ℤ) = l * Nat.gcdA l m + m * Nat.gcdB l m := by
    have := Nat.gcd_eq_gcd_ab l m
    rw [h] at this
    exact_mod_cast this
  have hC : (1 : C) = (l : C) * (Nat.gcdA l m : C) + (m : C) * (Nat.gcdB l m : C) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : C)) hb
  have h1 : 0 < v ((l : C) * (Nat.gcdA l m : C)) := by
    rw [v.map_mul, hv]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (val_intCast_nonneg v _))
  have h2 : 0 < v ((m : C) * (Nat.gcdB l m : C)) := by
    rw [v.map_mul]
    exact lt_of_lt_of_le hm (le_add_of_nonneg_right (val_intCast_nonneg v _))
  have h3 := v.map_lt_add h1 h2
  rw [← hC, v.map_one] at h3
  exact lt_irrefl _ h3
end GlobalTheory.OddBlock.BlockContent
