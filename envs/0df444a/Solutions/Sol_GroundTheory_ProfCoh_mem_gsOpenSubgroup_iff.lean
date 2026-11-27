-- Prove2me | solution 1 for GroundTheory.ProfCoh.mem_gsOpenSubgroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:49:31.363446+00:00
-- url     : https://prove2.me/submissions/16730a7b-974c-45f2-a202-57279b56d902

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
theorem _root_.solution (σ : galUnramifiedOutside F Ω S) :
    σ ∈ gsOpenSubgroup S hL ↔ ∀ x : L, σ (gsEmbedding hL x) = gsEmbedding hL x :=
  mem_fixingOfRestrictScalarsEq_iff _ σ
end GroundTheory.ProfCoh
