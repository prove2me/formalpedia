-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_add_eq_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:48:31.061801+00:00
-- url     : https://prove2.me/submissions/f3f66f19-1816-4afd-bc79-83bf6f550bc1

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
theorem _root_.solution {x y : Ω} (h : nrm K y < nrm K x) : nrm K (x + y) = nrm K x := by
  letI := algebraicNormedField K Ω
  haveI := algebraicNormedField_isUltrametricDist K Ω
  change ‖y‖ < ‖x‖ at h
  change ‖x + y‖ = ‖x‖
  exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt h) |>.trans (max_eq_left h.le)
end GroundTheory.PAdicHodge
