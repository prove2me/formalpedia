-- Prove2me | solution 1 for GroundTheory.ProfCoh.fieldEquivOfRestrictScalarsEq_apply_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:04:54.480899+00:00
-- url     : https://prove2.me/submissions/cf277ba6-f892-40bd-b09d-56199261e3f5

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
theorem _root_.solution (σ : fixingOfRestrictScalarsEq h) (x : E) :
    fieldEquivOfRestrictScalarsEq h ((σ : Gal(E/F)) x) =
      fixingMulEquivOfRestrictScalarsEq h σ (fieldEquivOfRestrictScalarsEq h x) :=
  rfl
end GroundTheory.ProfCoh
