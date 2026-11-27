-- Prove2me | solution 1 for GlobalTheory.AnValPh1.jetOf_sum_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:08:56.817924+00:00
-- url     : https://prove2.me/submissions/a2579a94-06e6-4804-a1ff-182a7d550ad8

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
import Theorems.Thm_GlobalTheory_AnValPh1_jetOf_coord
import Theorems.Thm_GlobalTheory_JetLinSub_jetOf_coord


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
theorem _root_.solution {N : ℕ} (m : ℕ) {T : Type} (I : Finset T) (k : T → Fin N) :
    jetOf m (fun v : Fin N → ℂ => ∑ i ∈ I, v (k i)) =
      Ideal.Quotient.mk _ (∑ i ∈ I, MvPolynomial.X ((0 : Fin 1), k i)) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using jetOf_const (g := N) m 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha, map_add]
    rw [← ih, ← jetOf_coord, ← jetOf_add]
    · rfl
    · exact (contDiff_apply ℂ ℂ _).contDiffAt
    · exact (ContDiff.sum fun i _ => contDiff_apply ℂ ℂ _).contDiffAt
end GlobalTheory.AnValPh1
