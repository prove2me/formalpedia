-- Prove2me | solution 1 for GlobalTheory.AnValJetEx.jetOf_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:17:19.665915+00:00
-- url     : https://prove2.me/submissions/b317352a-7b59-4f51-a1cc-ca44abbf0401

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
theorem _root_.solution {d : ℕ} (m : ℕ) {K : Type} (s : Finset K) {f : K → (Fin d → ℂ) → ℂ}
    (hf : ∀ k, ContDiffAt ℂ ω (f k) 0) :
    jetOf m (fun z => ∏ k ∈ s, f k z) = ∏ k ∈ s, jetOf m (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jetOf_one m
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, ← jetOf_mul m (hf a) (contDiffAt_prod fun k _ => hf k)]
    congr 1
    funext z
    simp [Finset.prod_insert ha]
end GlobalTheory.AnValJetEx
