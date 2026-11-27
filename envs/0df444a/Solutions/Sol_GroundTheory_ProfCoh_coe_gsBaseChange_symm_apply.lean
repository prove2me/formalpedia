-- Prove2me | solution 1 for GroundTheory.ProfCoh.coe_gsBaseChange_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:49:33.985147+00:00
-- url     : https://prove2.me/submissions/6e96c27a-519f-4df4-8831-ed85851f2bb2

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_BaseChangeDefs
import Theorems.Thm_GroundTheory_ProfCoh_coe_fixingMulEquivOfRestrictScalarsEq_symm_apply

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
theorem _root_.solution (τ : galUnramifiedOutside L Ω (placesOver S))
    (x : maxUnramifiedOutside F Ω S) :
    (((((gsBaseChange S hL).symm τ : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))) : galUnramifiedOutside F Ω S) x :
        maxUnramifiedOutside F Ω S) : Ω) = (τ (gsFieldEquiv hL x) : Ω) :=
  coe_fixingMulEquivOfRestrictScalarsEq_symm_apply _ τ x
end GroundTheory.ProfCoh
