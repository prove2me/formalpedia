-- Prove2me | solution 1 for GlobalTheory.AnVal.Sym.tay_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:11:38.91477+00:00
-- url     : https://prove2.me/submissions/c383b02e-c50a-4e59-8cc1-e758b6733b3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProductsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AnalyticFrameSymmetryTrivial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_eq_of_cc
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
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.Sym
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnVal.Sym
theorem _root_.solution {g : ℕ} (k : Fin g) :
    tay (fun v : Fin g → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  have hc : ContDiffAt ℂ ω (fun v : Fin g → ℂ => v k) 0 := (contDiff_apply ℂ ℂ k).contDiffAt
  refine TCPf.eq_of_cc _ _ fun l => ?_
  rcases List.eq_nil_or_concat l with rfl | ⟨l', q, rfl⟩
  · simp only [List.foldr_nil, constantCoeff_tay, MvPowerSeries.constantCoeff_X]
    show lD _ 0 (Multiset.toList 0) = 0
    rw [Multiset.toList_zero]
    exact iteratedFDeriv_zero_apply _
  · rw [List.concat_eq_append, List.foldr_append, List.foldr_append]
    congr 2
    obtain ⟨a, j⟩ := q
    obtain rfl : a = 0 := Subsingleton.elim _ _
    simp only [List.foldr_cons, List.foldr_nil]
    rw [TM.pderiv_tay hc]
    have : (fun y : Fin g → ℂ => fderiv ℂ (fun v : Fin g → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j (1 : ℂ) : Fin g → ℂ) k := by
      funext y
      rw [(hasFDerivAt_apply (𝕜 := ℂ) k y).fderiv]
      rfl
    rw [this, TM.tay_const, MvPowerSeries.pderiv_X]
    by_cases h : k = j
    · subst h; simp
    · simp [h, Pi.single_apply]
end GlobalTheory.AnVal.Sym
