-- Prove2me | solution 1 for GlobalTheory.ChartGlue.contDiffOn_log_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:30:38.403458+00:00
-- url     : https://prove2.me/submissions/a465fc82-468d-4bb5-862f-6c59aab956c4

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Theorems.Thm_GlobalTheory_ChartGlue_contDiffOn_real

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
open MeasureTheory Set Filter Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff ENNReal
open GlobalTheory GlobalTheory.ChartGlue
variable {n : ℕ} {X : Type*} [TopologicalSpace X] {ι : Type*}
namespace GlobalTheory.ChartGlue
theorem _root_.solution {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (h0 : ∀ v ∈ U, g v ≠ 0) :
    ContDiffOn ℝ ∞ (fun v => Real.log (‖g v‖ ^ 2)) U :=
  ((contDiffOn_real hU hg).norm_sq ℂ).log fun v hv => pow_ne_zero _ (norm_ne_zero_iff.2 (h0 v hv))
end GlobalTheory.ChartGlue
