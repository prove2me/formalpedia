-- Prove2me | solution 1 for GlobalTheory.GlueCover.volume_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:34:50.425877+00:00
-- url     : https://prove2.me/submissions/a24438e8-9414-45e3-a8ce-d4635713a969

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormula

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
namespace GlobalTheory.GlueCover
theorem _root_.solution (hn : n ≠ 0) {S : Set (V n)} (hS : S.Finite) : volume S = 0 := by
  haveI : NeZero n := ⟨hn⟩
  haveI : Nonempty (Fin n) := inferInstance
  haveI : Nontrivial (V n) := inferInstance
  exact hS.measure_zero volume
end GlobalTheory.GlueCover
