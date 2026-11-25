-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_natCast_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:08:29.951145+00:00
-- url     : https://prove2.me/submissions/49afc7e8-4d09-4f91-81aa-70854f3fec64

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower

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
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
variable {K}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (n : ℕ) : nrm K (n : Ω) ≤ 1 := by
  letI := algebraicNormedField K Ω
  haveI := algebraicNormedField_isUltrametricDist K Ω
  change ‖(n : Ω)‖ ≤ 1
  exact IsUltrametricDist.norm_natCast_le_one Ω n
end GroundTheory.PAdicHodge
