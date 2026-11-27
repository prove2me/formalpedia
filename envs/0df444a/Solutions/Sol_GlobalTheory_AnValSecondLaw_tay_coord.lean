-- Prove2me | solution 1 for GlobalTheory.AnValSecondLaw.tay_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:35:43.750083+00:00
-- url     : https://prove2.me/submissions/70f0b7f0-a626-43ce-8eff-608777ed6c38

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_eq_of_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_mD_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_pderiv_tay
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_tay_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_constantCoeff_tay


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
theorem _root_.solution {N : ℕ} (k : Fin N) :
    tay (fun v : Fin N → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  classical
  have hθ : ContDiffAt ℂ ω (fun v : Fin N → ℂ => v k) 0 := (contDiff_apply ℂ ℂ k).contDiffAt
  refine TCPf.eq_of_cc _ _ fun l => ?_
  induction l using List.reverseRecOn with
  | nil =>
    simp only [List.foldr_nil]
    rw [constantCoeff_tay, TM.mD_zero]
    simp
  | append_singleton l q _ =>
    obtain ⟨a, j⟩ := q
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    rw [List.foldr_append, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil]
    rw [TM.pderiv_tay hθ]
    have hd : (fun y : Fin N → ℂ => fderiv ℂ (fun v : Fin N → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j 1 : Fin N → ℂ) k := by
      funext y
      have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).fderiv (x := y)
      exact congrArg (fun L : (Fin N → ℂ) →L[ℂ] ℂ => L (Pi.single j 1)) this
    rw [hd, TM.tay_const, MvPowerSeries.pderiv_X]
    congr 2
    by_cases h : k = j
    · subst h; simp
    · simp [Pi.single_apply, h, Prod.ext_iff]
end GlobalTheory.AnValSecondLaw
