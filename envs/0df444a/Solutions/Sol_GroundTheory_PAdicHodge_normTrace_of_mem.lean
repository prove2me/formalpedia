-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:16.663067+00:00
-- url     : https://prove2.me/submissions/d9c94af6-d2ba-45e7-bb2b-df1ae1694ab6

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
theorem _root_.solution (k : IntermediateField B₀ Ω) {a : Ω} (ha : a ∈ k) : normTrace k a = a :=
  normTrace_algebraMap k ⟨a, ha⟩
end GroundTheory.PAdicHodge
