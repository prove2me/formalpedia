-- Prove2me | solution 1 for GlobalTheory.MatchTerm.txT_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:54:38.441105+00:00
-- url     : https://prove2.me/submissions/37d52134-84a3-4a36-8d56-792852229a8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationSeriesTermsNestStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLatticeIsoAndTermsAgree
import Theorems.Thm_GlobalTheory_T_norm_rep_generators_and_thetaSeriesTerm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Filter
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.MatchTerm
namespace GlobalTheory.MatchTerm
theorem _root_.solution {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ} (hq : N.Int q) {m : ℕ}
    (hm : Odd m) (p : N.QT (m ^ 2)) (hp : p.1.1 = 1) : Tendsto (N.txT m p) cofinite (𝓝 0) := by
  have h0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.pos.ne'
  refine squeeze_zero_norm (a := fun χ => Real.exp (-q χ)) (fun χ => ?_)
    (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hq.pos))
  rw [(GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hq).2 m hm p χ, hp, toAdd_one, zero_add, ← natCast_zsmul, QuadraticMap.map_smul]
  have : (((m : ℤ) * (m : ℤ)) • q χ) / (m : ℝ) ^ 2 = q χ := by
    rw [zsmul_eq_mul]; push_cast; field_simp
  rw [this]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (hq.th _)
end GlobalTheory.MatchTerm
