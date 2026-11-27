-- Prove2me | solution 1 for GlobalTheory.CubeReading.sum_finset_fin_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:15:42.894461+00:00
-- url     : https://prove2.me/submissions/7c67e6d5-e2e8-420f-bd66-ddbd351d4b7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrame

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
theorem _root_.solution (f : Finset (Fin 3) → ℂ) :
    ∑ I : ULift.{0} (Finset (Fin 3)), f I.down =
      f ∅ + f {0} + f {1} + f {2} + f {0, 1} + f {0, 2} + f {1, 2} + f {0, 1, 2} := by
  rw [← Equiv.sum_comp Equiv.ulift.symm]
  simp only [Equiv.ulift_symm_down]
  have hu : (Finset.univ : Finset (Finset (Fin 3))) =
      (insert 0 (insert 1 (insert 2 ∅)) : Finset (Fin 3)).powerset := by
    rw [← Finset.powerset_univ]; rfl
  rw [hu]
  simp only [Finset.sum_powerset_insert (show (0 : Fin 3) ∉ insert 1 (insert 2 ∅) by decide),
    Finset.sum_powerset_insert (show (1 : Fin 3) ∉ insert 2 ∅ by decide),
    Finset.sum_powerset_insert (show (2 : Fin 3) ∉ (∅ : Finset (Fin 3)) by decide),
    Finset.powerset_empty, Finset.sum_singleton]
  simp only [Finset.insert_empty]
  ring
end GlobalTheory.CubeReading
