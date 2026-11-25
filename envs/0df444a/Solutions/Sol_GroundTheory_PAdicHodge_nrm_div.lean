-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:50:38.365561+00:00
-- url     : https://prove2.me/submissions/7db816a2-4a1c-4f2d-b916-0019ac18ee0b

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
theorem _root_.solution (x y : Ω) : nrm K (x / y) = nrm K x / nrm K y := by
  letI := algebraicNormedField K Ω
  change ‖x / y‖ = ‖x‖ / ‖y‖
  exact norm_div x y
end GroundTheory.PAdicHodge
