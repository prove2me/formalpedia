-- Prove2me | solution 1 for GlobalTheory.AnValSecondLaw.jetN_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:12:20.656794+00:00
-- url     : https://prove2.me/submissions/82c6ad1f-2b8c-495a-8e87-559a09c8070f

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
import Theorems.Thm_GlobalTheory_AnValSecondLaw_tay_coord
import Theorems.Thm_P2M_GlobalTheory_AnValSecondLaw_psJet_X__bd933b739032
import Theorems.Thm_GlobalTheory_JetLinSub_tay_coord


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
theorem _root_.solution {n g : ℕ} (m : ℕ) (i : Fin n) (j : Fin g) :
    jetN m (fun w : Fin n → Fin g → ℂ => w i j) = Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := by
  have h : jetOf m (fun v : Fin (n * g) → ℂ => v (finProdFinEquiv (i, j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), finProdFinEquiv (i, j))) := by
    rw [jetOf, tay_coord, psJet_X']
  show renN n g m (jetOf m (fun v : Fin (n * g) → ℂ => v (finProdFinEquiv (i, j)))) = _
  rw [h]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
  simp only [MvPolynomial.aeval_X, Equiv.symm_apply_apply]
end GlobalTheory.AnValSecondLaw
