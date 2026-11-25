-- Prove2me | solution 1 for GlobalTheory.OddBlock.ExpBinomial.real_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:53:08.377175+00:00
-- url     : https://prove2.me/submissions/3184d28b-d825-41f6-b94e-cbe6de66384a

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
open ReciprocityTheory.PGsh
noncomputable section
open GlobalTheory GlobalTheory.OddBlock GlobalTheory.OddBlock.ExpBinomial
namespace GlobalTheory.OddBlock.ExpBinomial
theorem _root_.solution {l : ℕ} (hl : 5 ≤ l) {L E n s K : ℕ} (hL : 1 ≤ L)
    (hE : (E : ℝ) = 1 + ((L : ℝ) - l) / ((l : ℝ) ^ 2 - 1)) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hK : K ≤ n * s) (p : ℝ) (hp0 : 0 ≤ p)
    (hp : 1 ≤ K → (K : ℝ) / (l - 1) - (n : ℝ) ^ 2 * (Real.logb l K + 1) ≤ p) :
    (s : ℝ) / 8 - (n : ℝ) ^ 2 * (Real.logb l (n * s) + 1) ≤
      ((E * K + (s - K) : ℕ) : ℝ) + (p + (0 - ((1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (L : ℝ))) * (L * K) +
        (1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (L : ℝ))) * K))) := by
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hns : (1 : ℝ) ≤ (n : ℝ) * s := by exact_mod_cast Nat.mul_le_mul hn hs
  have hlog : 0 ≤ Real.logb l (n * s) := Real.logb_nonneg (by linarith) hns
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have hs0 : (0 : ℝ) ≤ s := by positivity
  rcases Nat.eq_zero_or_pos K with rfl | hK1
  · have := mul_nonneg hn2 (show 0 ≤ Real.logb l (n * s) + 1 by linarith)
    simp only [mul_zero, Nat.sub_zero, zero_add, Nat.cast_zero, add_zero, sub_zero]
    linarith
  · have hp1 := hp hK1
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have hlog2 : Real.logb l K ≤ Real.logb l (n * s) :=
      Real.logb_le_logb_of_le (by linarith) (by linarith) (by exact_mod_cast hK)
    have h3 := mul_le_mul_of_nonneg_left hlog2 hn2
    have h4 : (s : ℝ) ≤ ((s - K : ℕ) : ℝ) + K := by exact_mod_cast (by omega : s ≤ s - K + K)
    have h5 : (0 : ℝ) ≤ ((s - K : ℕ) : ℝ) := by positivity
    have h1 : (l : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (l : ℝ) + 1 ≠ 0 := by linarith
    have h6 : (1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (L : ℝ))) * (L * K) +
        (1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (L : ℝ))) * K =
        E * K + K / (l - 1) - K / 8 - K / (8 * L) := by
      rw [hE, show (l : ℝ) ^ 2 - 1 = (l - 1) * (l + 1) by ring]
      field_simp
      ring
    have h7 : (0 : ℝ) ≤ K / (8 * L) := by positivity
    rw [h6, Nat.cast_add, Nat.cast_mul]
    linarith
end GlobalTheory.OddBlock.ExpBinomial
