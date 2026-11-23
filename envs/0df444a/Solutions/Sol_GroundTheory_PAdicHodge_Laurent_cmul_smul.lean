-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.cmul_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:13.46113+00:00
-- url     : https://prove2.me/submissions/2ed65bb6-5ae8-4325-9c3c-2ff24e2e43bb

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries

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
variable [CompleteSpace K]
namespace GroundTheory.PAdicHodge.Laurent
theorem _root_.solution (k : K) (a b : ℤ → K) : cmul a (k • b) = k • cmul a b := by
  funext n
  simp only [cmul, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  congr 1; funext i; ring
end GroundTheory.PAdicHodge.Laurent
