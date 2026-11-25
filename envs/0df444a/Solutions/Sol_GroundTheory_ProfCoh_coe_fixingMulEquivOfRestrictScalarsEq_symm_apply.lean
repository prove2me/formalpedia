-- Prove2me | solution 1 for GroundTheory.ProfCoh.coe_fixingMulEquivOfRestrictScalarsEq_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:02:18.644605+00:00
-- url     : https://prove2.me/submissions/de035193-5d16-4c03-82c2-a3aa47ddf9c0

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
theorem _root_.solution (τ : Gal(E'/L)) (x : E) :
    (((((fixingMulEquivOfRestrictScalarsEq h).symm τ : fixingOfRestrictScalarsEq h) : Gal(E/F)) x :
      E) : Ω) = (τ (fieldEquivOfRestrictScalarsEq h x) : Ω) :=
  rfl
end GroundTheory.ProfCoh
