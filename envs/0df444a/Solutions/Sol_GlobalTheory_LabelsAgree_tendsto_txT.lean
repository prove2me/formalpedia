-- Prove2me | solution 1 for GlobalTheory.LabelsAgree.tendsto_txT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:35:04.482957+00:00
-- url     : https://prove2.me/submissions/3a257f0e-7287-4abd-96ba-58e3ba59b1f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SymmPairingEqOneOfOddOfDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisUniqueMinPairSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLabelsAgreeOfIso
import Theorems.Thm_GlobalTheory_T_norm_rep_generators_and_thetaSeriesTerm
import Theorems.Thm_GlobalTheory_TorsionFourier_add_nsmul_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory GlobalTheory.LabelsAgree
namespace GlobalTheory.LabelsAgree
theorem _root_.solution {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ} (hI : N.Int q) {m : ℕ}
    (hm : Odd m) (p : N.QT (m ^ 2)) : Filter.Tendsto (N.txT m p) Filter.cofinite (nhds 0) := by
  have hm0 : 0 < m := hm.pos
  have h1 := hI.pos.comp (TorsionFourier.add_nsmul_injective hm0 p.1.1.toAdd).tendsto_cofinite
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (h1.atTop_div_const (r := (m : ℝ) ^ 2) (by positivity))
  refine squeeze_zero_norm (fun χ => ?_) h2
  rw [(GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 m hm p χ]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (hI.th _)
end GlobalTheory.LabelsAgree
