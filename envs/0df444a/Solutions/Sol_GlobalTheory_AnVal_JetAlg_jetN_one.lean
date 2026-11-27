-- Prove2me | solution 1 for GlobalTheory.AnVal.JetAlg.jetN_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:39:38.148617+00:00
-- url     : https://prove2.me/submissions/7951854d-7bc7-4c0f-82cd-03e1f1768a88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_taylor_multiplication


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetAlg
namespace GlobalTheory.AnVal.JetAlg
theorem _root_.solution {n g : ℕ} (m : ℕ) : jetN m (fun _ : Fin n → Fin g → ℂ => (1 : ℂ)) = 1 := by
  have hc := TM.taylor_multiplication.2.1 (n * g) 1
  simp only [jetN, jetOf]
  rw [hc, map_one, FBIdJet.psJet_one, map_one]
end GlobalTheory.AnVal.JetAlg
