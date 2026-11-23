-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.domSet_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:39.581865+00:00
-- url     : https://prove2.me/submissions/ffa93669-7653-4006-ab84-47089bab0154

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_finite_le
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
variable (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0)
include hρ h ha
namespace GroundTheory.PAdicHodge.Laurent
theorem _root_.solution : (domSet a ρ).Finite :=
  (h.finite_le (gaussNorm_pos hρ h ha)).subset fun n hn => le_of_eq (Eq.symm hn)
end GroundTheory.PAdicHodge.Laurent
