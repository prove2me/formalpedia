-- Prove2me | solution 1 for GlobalTheory.CosetCrit.norm_tx_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:11:17.442513+00:00
-- url     : https://prove2.me/submissions/14f5adb4-fba0-4d61-b878-f6de27647701

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorsionTwistTsumNormGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterion
import Theorems.Thm_GlobalTheory_CosetCrit_norm_txT_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.CosetCrit
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
  {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}
omit [CompleteSpace C] [IsAlgClosed C]
namespace GlobalTheory.CosetCrit
theorem _root_.solution (hI : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) {χ₀ : N.X}
    (h₀ : ∀ χ, q (p.1.1.toAdd + m • χ₀) ≤ q (p.1.1.toAdd + m • χ)) :
    ‖N.tx m p‖ ≤ Real.exp (-(q (p.1.1.toAdd + m • χ₀) / (m : ℝ) ^ 2)) := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (Real.exp_pos _).le fun χ => ?_
  refine (norm_txT_le hI hm p χ).trans (Real.exp_le_exp.2 (neg_le_neg ?_))
  exact div_le_div_of_nonneg_right (h₀ χ) (by positivity)
end GlobalTheory.CosetCrit
