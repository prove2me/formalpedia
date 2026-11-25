-- Prove2me | solution 1 for GlobalTheory.OddBlock.BlockContent.biWindow_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:43.436921+00:00
-- url     : https://prove2.me/submissions/16902ba8-92cf-4917-ae4f-94636bae1866

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
import Theorems.Thm_GlobalTheory_OddBlock_BlockContent_biContent

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
theorem _root_.solution (hP : Formalism.L2.FormalSeriesBounds.ThmP) (hV : BiValue) : BiWindow := by
  intro C _ _ v l hl h5 hv i hi n0 n m hn h1n hm hr t t' h1 hH hM1 hM2 Y0
  obtain ⟨y, hy1, hy2, hy⟩ := (hP C v l hl h5 hv i hi n n0 (h1n.trans hn) hn h1 hM1 hM2).1 h1n Y0
  refine ⟨y, hy1, hy2, ?_⟩
  rw [hV C l i n0 n hn hr t t' h1 hH y]
  refine (biContent C v l hl h5 hv i n n0 y hi (h1n.trans hn) hn _ hy).trans ?_
  rw [WithTop.coe_le_coe]
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hd : (0 : ℝ) ≤ (l : ℝ) - 1 := by linarith
  have hm' : (n : ℝ) - n0 ≤ ((i : ℝ) + 1) * m := by
    have : ((n - n0 : ℕ) : ℝ) ≤ (((i + 1) * m : ℕ) : ℝ) := by exact_mod_cast hm
    rw [Nat.cast_sub hn] at this
    push_cast at this
    exact this
  gcongr
end GlobalTheory.OddBlock.BlockContent
