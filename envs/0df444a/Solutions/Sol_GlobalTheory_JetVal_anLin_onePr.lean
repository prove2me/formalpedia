-- Prove2me | solution 1 for GlobalTheory.JetVal.anLin_onePr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:09:04.594892+00:00
-- url     : https://prove2.me/submissions/35d8f9c8-7aec-4062-a4d5-68240931d0b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsValueAtJetPointCmFrameSection
import Theorems.Thm_GlobalTheory_JetVal_onePr_apply

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
open GlobalTheory GlobalTheory.JetVal
open AlgebraicGeometry CategoryTheory Opposite Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetVal
theorem _root_.solution {g : ℕ} (p : Fin 1 × Fin g) :
    anLin (onePr g) p = MvPolynomial.X ((0 : Fin 1), finProdFinEquiv ((0 : Fin 1), p.2)) := by
  rw [anLin, Finset.sum_eq_single (finProdFinEquiv ((0 : Fin 1), p.2))]
  · rw [onePr_apply, Pi.single_eq_same, map_one]
    exact _root_.one_mul _
  · intro k _ hk
    rw [onePr_apply, Pi.single_eq_of_ne (Ne.symm hk), map_zero, zero_mul]
  · simp
end GlobalTheory.JetVal
