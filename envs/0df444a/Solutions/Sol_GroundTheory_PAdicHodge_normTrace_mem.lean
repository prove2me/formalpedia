-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:50.825815+00:00
-- url     : https://prove2.me/submissions/b1d58c94-7cca-4000-a535-e6534c996e6e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable {B₀ Ω : Type*} [Field B₀] [Field Ω] [Algebra B₀ Ω]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (k : IntermediateField B₀ Ω) (y : Ω) : normTrace k y ∈ k :=
  (normTraceF k y).2
end GroundTheory.PAdicHodge
