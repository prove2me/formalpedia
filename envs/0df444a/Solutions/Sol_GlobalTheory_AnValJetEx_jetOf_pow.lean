-- Prove2me | solution 1 for GlobalTheory.AnValJetEx.jetOf_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:17:17.317352+00:00
-- url     : https://prove2.me/submissions/475515fd-aa6b-41a4-8cce-9041b8f9eec7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorJetReading
import Theorems.Thm_GlobalTheory_AnValJetEx_jetOf_one

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
theorem _root_.solution {d : ℕ} (m : ℕ) {f : (Fin d → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (k : ℕ) :
    jetOf m (fun z => f z ^ k) = jetOf m f ^ k := by
  induction k with
  | zero => simpa using jetOf_one m
  | succ k ih =>
    rw [pow_succ, ← ih, ← jetOf_mul m (hf.pow k) hf]
    congr 1
end GlobalTheory.AnValJetEx
