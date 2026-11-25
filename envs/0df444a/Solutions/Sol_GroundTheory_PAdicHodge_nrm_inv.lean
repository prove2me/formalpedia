-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:50:40.769641+00:00
-- url     : https://prove2.me/submissions/59b20393-afa4-4d3f-a12e-e6c31033f6ba

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
theorem _root_.solution (x : Ω) : nrm K x⁻¹ = (nrm K x)⁻¹ := by
  letI := algebraicNormedField K Ω
  change ‖x⁻¹‖ = ‖x‖⁻¹
  exact norm_inv x
end GroundTheory.PAdicHodge
