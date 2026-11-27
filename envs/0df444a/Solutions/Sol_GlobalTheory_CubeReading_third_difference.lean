-- Prove2me | solution 1 for GlobalTheory.CubeReading.third_difference
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:47:26.61023+00:00
-- url     : https://prove2.me/submissions/eb69bf20-ea6c-4b84-a440-45aa97565b8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrame
import Theorems.Thm_GlobalTheory_CubeReading_psumL_apply
import Theorems.Thm_GlobalTheory_CubeReading_sum_finset_fin_three

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.CubeReading
namespace GlobalTheory.CubeReading
theorem _root_.solution {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin 3 → Fin g → ℂ) :
    ∑ I : thK, ((thε I : ℤ) : ℂ) * hermForm Hm (psumL 3 g I z) (psumL 3 g I w) = 0 := by
  have hs : ∀ f : Finset (Fin 3) → ℂ, ∑ I : thK, f I.down =
      f ∅ + f {0} + f {1} + f {2} + f {0, 1} + f {0, 2} + f {1, 2} + f {0, 1, 2} :=
    fun f => sum_finset_fin_three f
  have he : ∀ J : Finset (Fin 3), thε (ULift.up J : ULift.{0} (Finset (Fin 3))) = (-1) ^ (3 - J.card) :=
    fun J => rfl
  refine (hs fun J => ((thε (ULift.up J : ULift.{0} (Finset (Fin 3))) : ℤ) : ℂ) *
      hermForm Hm (psumL 3 g (ULift.up J) z) (psumL 3 g (ULift.up J) w)).trans ?_
  simp only [he, psumL_apply]
  simp [Finset.sum_insert, hermForm, add_dotProduct, dotProduct_add, Matrix.mulVec_add, star_add]
  ring
end GlobalTheory.CubeReading
