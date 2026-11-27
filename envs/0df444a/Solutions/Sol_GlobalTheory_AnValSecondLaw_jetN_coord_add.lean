-- Prove2me | solution 1 for GlobalTheory.AnValSecondLaw.jetN_coord_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:20:24.879991+00:00
-- url     : https://prove2.me/submissions/119cdc88-3393-428d-bcde-fcfa4ee49cd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProducts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppLESpMapJetPt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AnalyticFrameSecondPartialLawTrivial
import Theorems.Thm_GlobalTheory_AnValSecondLaw_jetN_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AnValSecondLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
namespace GlobalTheory.AnValSecondLaw
theorem _root_.solution {n g : ℕ} (m : ℕ) (i i' : Fin n) (j : Fin g) :
    jetN m (fun w : Fin n → Fin g → ℂ => w i j + w i' j) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, j) + MvPolynomial.X (i', j)) := by
  rw [map_add, ← jetN_coord, ← jetN_coord, jetN, jetN, jetN, ← map_add]
  exact congrArg _ (jetOf_add m (contDiff_apply ℂ ℂ (finProdFinEquiv (i, j))).contDiffAt
      (contDiff_apply ℂ ℂ (finProdFinEquiv (i', j))).contDiffAt)
end GlobalTheory.AnValSecondLaw
