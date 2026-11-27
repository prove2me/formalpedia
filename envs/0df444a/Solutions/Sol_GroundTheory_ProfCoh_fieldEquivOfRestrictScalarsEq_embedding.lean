-- Prove2me | solution 1 for GroundTheory.ProfCoh.fieldEquivOfRestrictScalarsEq_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:20.0931+00:00
-- url     : https://prove2.me/submissions/c7b6fbbd-8701-45b0-be4c-232c753d63ba

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_BaseChangeDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
universe u
noncomputable section
variable {F L Ω : Type u} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω] {E : IntermediateField F Ω} {E' : IntermediateField L Ω}
  (h : E'.restrictScalars F = E)
namespace GroundTheory.ProfCoh
theorem _root_.solution (x : L) :
    fieldEquivOfRestrictScalarsEq h (embeddingOfRestrictScalarsEq h x) = algebraMap L E' x :=
  rfl
end GroundTheory.ProfCoh
