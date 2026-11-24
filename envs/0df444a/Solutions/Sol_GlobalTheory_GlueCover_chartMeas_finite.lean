-- Prove2me | solution 1 for GlobalTheory.GlueCover.chartMeas_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:09:32.509222+00:00
-- url     : https://prove2.me/submissions/88d4b0e0-0705-49a5-8fc0-ac5380f66dfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormula
import Theorems.Thm_GlobalTheory_GlueCover_volume_finite

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
open MeasureTheory Set Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
open GlobalTheory GlobalTheory.GlueCover
open GlobalTheory.ChartGlue
variable {n : ℕ}
variable {X ι : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
namespace GlobalTheory.GlueCover
theorem _root_.solution (hn : n ≠ 0) (e : OpenPartialHomeomorph X (V n)) (ρ : X → ℝ≥0∞)
    {F : Set X} (hF : F.Finite) : chartMeas e ρ F = 0 := by
  rw [chartMeas_apply e ρ hF.measurableSet]
  exact setLIntegral_measure_zero _ _ (volume_finite hn ((hF.inter_of_right _).image _))
end GlobalTheory.GlueCover
