-- Prove2me | solution 1 for GroundTheory.ProfCoh.coe_gsBaseChange_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:49:31.824387+00:00
-- url     : https://prove2.me/submissions/12a712a9-064d-435f-80eb-dc3f175048cd

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_BaseChangeDefs
import Theorems.Thm_GroundTheory_ProfCoh_coe_fixingMulEquivOfRestrictScalarsEq_apply

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
variable {S}
namespace GroundTheory.ProfCoh
theorem _root_.solution (σ : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)))
    (x : maxUnramifiedOutside L Ω (placesOver S)) :
    ((gsBaseChange S hL σ x : maxUnramifiedOutside L Ω (placesOver S)) : Ω) =
      ((σ : galUnramifiedOutside F Ω S) ((gsFieldEquiv hL).symm x) : Ω) :=
  coe_fixingMulEquivOfRestrictScalarsEq_apply _ σ x
end GroundTheory.ProfCoh
