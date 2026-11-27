-- Prove2me | solution 1 for GroundTheory.ProfCoh.coe_gsOpenSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:49:37.419797+00:00
-- url     : https://prove2.me/submissions/6531a722-1882-4c7a-8181-5d25ba1dbc84

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
variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)
namespace GroundTheory.ProfCoh
theorem _root_.solution : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) =
    fixingOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL) :=
  rfl
end GroundTheory.ProfCoh
