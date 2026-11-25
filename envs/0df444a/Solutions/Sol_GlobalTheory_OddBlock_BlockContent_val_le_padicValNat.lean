-- Prove2me | solution 1 for GlobalTheory.OddBlock.BlockContent.val_le_padicValNat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:15:13.879847+00:00
-- url     : https://prove2.me/submissions/422e51be-8619-4def-b867-f36a5ecb2494

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
import Theorems.Thm_GlobalTheory_OddBlock_BlockContent_val_coprime_le
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_GlobalTheory_BlockValue_Lead_mul
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_mul


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
theorem _root_.solution {l N : ℕ} (hl : l.Prime) (hv : v (l : C) = 1) (hN : N ≠ 0) :
    v (N : C) ≤ ((padicValNat l N : ℝ) : WithTop ℝ) := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN l hl.ne_one
  haveI := Fact.mk hl
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  rw [padicValNat.mul (pow_ne_zero _ hl.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero, Nat.cast_mul, Nat.cast_pow, v.map_mul, v.map_pow, hv]
  have := val_coprime_le v hv ((Nat.Prime.coprime_iff_not_dvd hl).2 hm)
  calc e • (1 : WithTop ℝ) + v (m : C) ≤ e • (1 : WithTop ℝ) + 0 := by gcongr
    _ = _ := by simp
end GlobalTheory.OddBlock.BlockContent
