-- Prove2me | solution 1 for GlobalTheory.AnValPh1.jetN_psum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:19:40.149128+00:00
-- url     : https://prove2.me/submissions/088415d0-f2b3-4d8e-a23b-db8c704ec5e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProductsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppLESpMapJetPt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AnalyticFrameFirstPartialLawTrivial
import Theorems.Thm_GlobalTheory_AnValPh1_jetOf_sum_coord
import Theorems.Thm_GlobalTheory_AnValPh1_psumL_apply
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk
import Theorems.Thm_GlobalTheory_CubeReading_psumL_apply


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
open GlobalTheory GlobalTheory.AnValPh1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnValPh1
theorem _root_.solution {n g : ℕ} (m : ℕ) (I : Finset (Fin n)) (j : Fin g) :
    jetN m (fun w => psumL n g ⟨I⟩ w j) = Ideal.Quotient.mk _ (∑ i ∈ I, MvPolynomial.X (i, j)) := by
  have : (fun v => psumL n g ⟨I⟩ (colsOf n g v) j) = fun v : Fin (n * g) → ℂ => ∑ i ∈ I, v (finProdFinEquiv (i, j)) := by
    funext v
    rw [psumL_apply, Finset.sum_apply]; rfl
  rw [jetN, this, jetOf_sum_coord, renN, GermD.jetMap_mk]
  simp only [map_sum, MvPolynomial.aeval_X, Equiv.symm_apply_apply]
end GlobalTheory.AnValPh1
