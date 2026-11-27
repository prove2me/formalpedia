-- Prove2me | solution 1 for GroundTheory.ProfCoh.gsFieldEquiv_apply_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:52.94988+00:00
-- url     : https://prove2.me/submissions/f7eeb56b-322c-419a-8e2d-fa1de193637f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_BaseChangeDefs
import Theorems.Thm_GroundTheory_ProfCoh_fieldEquivOfRestrictScalarsEq_apply_apply

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
    (x : maxUnramifiedOutside F Ω S) :
    gsFieldEquiv hL ((σ : galUnramifiedOutside F Ω S) x) = gsBaseChange S hL σ (gsFieldEquiv hL x) :=
  fieldEquivOfRestrictScalarsEq_apply_apply _ σ x
end GroundTheory.ProfCoh
