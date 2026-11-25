-- Prove2me | solution 1 for GroundTheory.PAdicHodge.abs_nrm_sub_nrm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:10.876611+00:00
-- url     : https://prove2.me/submissions/bf83e45e-c173-42d5-9df6-4f72b3248517

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
theorem _root_.solution (x y : Ω) : |nrm K x - nrm K y| ≤ nrm K (x - y) := by
  letI := algebraicNormedField K Ω
  change |‖x‖ - ‖y‖| ≤ ‖x - y‖
  exact abs_norm_sub_norm_le x y
end GroundTheory.PAdicHodge
