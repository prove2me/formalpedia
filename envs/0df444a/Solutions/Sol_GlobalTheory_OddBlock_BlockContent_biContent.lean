-- Prove2me | solution 1 for GlobalTheory.OddBlock.BlockContent.biContent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:43:37.970208+00:00
-- url     : https://prove2.me/submissions/c4c4cff1-e5e0-4499-91ac-458cb6975b56

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
import Theorems.Thm_GlobalTheory_OddBlock_BlockContent_val_factorial_le
import Theorems.Thm_GlobalTheory_OddBlock_BlockContent_slope_nonneg

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
theorem _root_.solution : BiContent := by
  intro C _ _ v l hl h5 hv i n n0 y hi hn hn0 Λ hΛ
  have h1 := val_factorial_le v hl hv (l ^ i * y)
  have h2 := val_factorial_le v hl hv y
  have hs := slope_nonneg (l := l) (i := i) hl.two_le hi.pos
  rw [v.map_mul, Nat.cast_pow, v.map_pow, Nat.cast_mul, v.map_mul]
  refine (add_le_add (nsmul_le_nsmul_right (add_le_add h1 h2) (n - n0)) hΛ).trans ?_
  rw [← WithTop.coe_add, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_le_coe, nsmul_eq_mul,
    Nat.cast_sub hn0]
  unfold bdP
  have hle : (n0 : ℝ) ≤ n := by exact_mod_cast hn0
  have h3 : (n0 : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) ≤
      (n : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) := by gcongr
  have h4 : ((n : ℝ) - n0) * ((((l ^ i * y : ℕ) : ℝ)) / ((l : ℝ) - 1) + (y : ℝ) / ((l : ℝ) - 1)) =
      ((n : ℝ) - n0) * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1) := by
    push_cast; ring
  linarith
end GlobalTheory.OddBlock.BlockContent
