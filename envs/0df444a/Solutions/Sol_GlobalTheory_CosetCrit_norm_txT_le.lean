-- Prove2me | solution 1 for GlobalTheory.CosetCrit.norm_txT_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:24:57.243137+00:00
-- url     : https://prove2.me/submissions/7efeb7c6-1311-406c-8eb0-98b20d378da6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorsionTwistTsumNormGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterion
import Theorems.Thm_GlobalTheory_T_norm_rep_generators_and_thetaSeriesTerm


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
omit [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
namespace GlobalTheory.CosetCrit
theorem _root_.solution (hI : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (χ : N.X) :
    ‖N.txT m p χ‖ ≤ Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) := by
  rw [(GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 m hm p χ]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (hI.th _)
end GlobalTheory.CosetCrit
