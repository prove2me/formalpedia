-- Prove2me | solution 1 for GlobalTheory.OddBlock.BlockContent.val_factorial_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:31:44.128248+00:00
-- url     : https://prove2.me/submissions/a5d27e53-c6f2-4c76-8ca5-6f0092953940

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
import Theorems.Thm_GlobalTheory_OddBlock_BlockContent_val_le_padicValNat

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
theorem _root_.solution {l : ℕ} (hl : l.Prime) (hv : v (l : C) = 1) (N : ℕ) :
    v ((N.factorial : ℕ) : C) ≤ (((N : ℝ) / ((l : ℝ) - 1) : ℝ) : WithTop ℝ) := by
  refine (val_le_padicValNat v hl hv N.factorial_ne_zero).trans ?_
  haveI := Fact.mk hl
  have h := sub_one_mul_padicValNat_factorial (p := l) N
  have h2 : (l - 1) * padicValNat l N.factorial ≤ N := h ▸ Nat.sub_le _ _
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have h3 : ((l : ℝ) - 1) * (padicValNat l N.factorial : ℝ) ≤ N := by
    have : (((l - 1) * padicValNat l N.factorial : ℕ) : ℝ) ≤ N := by exact_mod_cast h2
    rwa [Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_one] at this
  rw [WithTop.coe_le_coe, le_div_iff₀ (by linarith)]
  linarith
end GlobalTheory.OddBlock.BlockContent
