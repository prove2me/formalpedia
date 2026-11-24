-- Prove2me | solution 1 for GlobalTheory.T.exists_compact_open_units_subgroup_continuous_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:59.760261+00:00
-- url     : https://prove2.me/submissions/f9cce6ab-f37d-4be8-a1fb-61bf4c3537b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsCompactOpenUnitsSubgroupContinuousSqrt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsCompactOpenUnitsSubgroupContinuousSqrtStatement
import Theorems.Thm_GlobalTheory_QuadFibre_exists_isSqrtOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K], (2 : K) ≠ 0 → ∃ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s := by
  first | exact @GlobalTheory.QuadFibre.exists_isSqrtOn | exact GlobalTheory.QuadFibre.exists_isSqrtOn | (intros; apply GlobalTheory.QuadFibre.exists_isSqrtOn <;> assumption)
end _root_.GlobalTheory.T
