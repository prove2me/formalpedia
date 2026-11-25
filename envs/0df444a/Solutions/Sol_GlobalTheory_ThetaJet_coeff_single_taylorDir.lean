-- Prove2me | solution 1 for GlobalTheory.ThetaJet.coeff_single_taylorDir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:05:57.191285+00:00
-- url     : https://prove2.me/submissions/f3d4f0e0-5478-4c1d-8a8a-feac2fe1c244

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
open GlobalTheory.ThetaJet
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.ThetaJet
theorem _root_.solution {σ W : Type*} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (u : σ → W) {F : W → ℂ} (hF : AnalyticAt ℂ F 0) (i : σ) :
    MvPowerSeries.coeff (Finsupp.single i 1) (taylorDir u F) = fderiv ℂ F 0 (u i) := by
  have h := congrArg MvPowerSeries.constantCoeff (taylorDir_fderiv u hF i)
  rw [constantCoeff_taylorDir, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_pderiv] at h
  simpa using h.symm
end GlobalTheory.ThetaJet
