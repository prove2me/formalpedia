-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:06:58.679795+00:00
-- url     : https://prove2.me/submissions/71db7202-22df-4445-a374-0711d7a3afe7

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → Ω) :
    nrm K (∏ i ∈ s, f i) = ∏ i ∈ s, nrm K (f i) := by
  letI := algebraicNormedField K Ω
  change ‖∏ i ∈ s, f i‖ = ∏ i ∈ s, ‖f i‖
  exact norm_prod s f
end GroundTheory.PAdicHodge
