-- Prove2me | solution 1 for GlobalTheory.AnVal.JetAlg.AnO.zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:44:30.13172+00:00
-- url     : https://prove2.me/submissions/54f8c8cb-eedd-487b-97f2-bd5cece05df8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow

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
namespace AnO
theorem _root_.solution {n g : ℕ} {f : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (h0 : f (colsOf n g 0) ≠ 0) (k : ℤ) :
    AnO fun w => f w ^ k := by
  have hf' : ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0 := hf
  show ContDiffAt ℂ ω (fun v => f (colsOf n g v) ^ k) 0
  obtain ⟨p, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp only [zpow_natCast]
    exact hf'.pow p
  · simp only [zpow_neg, zpow_natCast]
    exact (hf'.pow p).inv (pow_ne_zero _ h0)
end AnO
end GlobalTheory.AnVal.JetAlg
