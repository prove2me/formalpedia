-- Prove2me | solution 1 for GlobalTheory.AnValJetEx.res_pullU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:38:24.72994+00:00
-- url     : https://prove2.me/submissions/190e24a6-2c9b-4605-9b5e-44dcb671d932

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorJetReading
import Theorems.Thm_P2M_GlobalTheory_AnValJetEx_res_res__7435de25bd2f

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
open GlobalTheory GlobalTheory.AnValJetEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnValJetEx
theorem _root_.solution {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U)
    (h' : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(X, U)ˣ) (b : Γ(Y, ⊤)ˣ) (hb : (f.appLE U ⊤ h').hom a.val = b.val) :
    res h (pullU f U a) = res (le_top : W ≤ ⊤) b := by
  have : b = res h' (pullU f U a) := Units.ext hb.symm
  rw [this, res_res']
end GlobalTheory.AnValJetEx
