-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.gaussNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:55.846809+00:00
-- url     : https://prove2.me/submissions/cbbc7167-f9ff-4beb-8119-8cc12a0c7a88

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
namespace GroundTheory.PAdicHodge.Laurent
theorem _root_.solution (hρ : 0 < ρ) : 0 ≤ gaussNorm a ρ :=
  Real.iSup_nonneg fun n => by positivity
end GroundTheory.PAdicHodge.Laurent
