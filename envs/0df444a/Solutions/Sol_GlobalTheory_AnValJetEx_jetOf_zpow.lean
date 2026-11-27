-- Prove2me | solution 1 for GlobalTheory.AnValJetEx.jetOf_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:26:05.619267+00:00
-- url     : https://prove2.me/submissions/1f929afd-9e00-4f47-836a-2da08116fb31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorJetReading
import Theorems.Thm_GlobalTheory_AnValJetEx_jetOf_one
import Theorems.Thm_GlobalTheory_AnValJetEx_jetOf_pow
import Theorems.Thm_P2M_GlobalTheory_AnValJetEx_contDiffAt_zpow__4224050d3ccb

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
theorem _root_.solution {d : ℕ} (m : ℕ) {f : (Fin d → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (h0 : f 0 ≠ 0)
    (u : (Jet ℂ (Fin 1 × Fin d) m)ˣ) (hu : u.val = jetOf m f) (k : ℤ) :
    jetOf m (fun z => f z ^ k) = (u ^ k).val := by
  cases k with
  | ofNat k => simpa [hu] using jetOf_pow m hf k
  | negSucc k =>
    rw [zpow_negSucc]
    refine Units.eq_inv_of_mul_eq_one_left ?_
    rw [Units.val_pow_eq_pow_val, hu, ← jetOf_pow m hf,
      ← jetOf_mul m (hf.pow (k + 1)) (contDiffAt_zpow' hf h0 _), ← jetOf_one m]
    refine jetOf_congr m ((hf.continuousAt.eventually_ne h0).mono fun z hz => ?_)
    show f z ^ (k + 1) * f z ^ (Int.negSucc k) = 1
    rw [zpow_negSucc, mul_inv_cancel₀ (pow_ne_zero _ hz)]
end GlobalTheory.AnValJetEx
