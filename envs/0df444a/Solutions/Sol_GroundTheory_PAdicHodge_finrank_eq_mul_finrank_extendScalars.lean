-- Prove2me | solution 1 for GroundTheory.PAdicHodge.finrank_eq_mul_finrank_extendScalars
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:53.130116+00:00
-- url     : https://prove2.me/submissions/4c7f4629-4e79-4aef-a4a2-7bcaa94a442a

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
theorem _root_.solution {k E : IntermediateField B₀ Ω} (h : k ≤ E) :
    finrank B₀ E = finrank B₀ k * finrank k (extendScalars h) := by
  rw [← relfinrank_eq_finrank_of_le h, ← relfinrank_bot_left, ← relfinrank_bot_left,
    relfinrank_mul_relfinrank bot_le h]
end GroundTheory.PAdicHodge
