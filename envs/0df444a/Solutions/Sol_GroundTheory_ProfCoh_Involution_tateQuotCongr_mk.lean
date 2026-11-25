-- Prove2me | solution 1 for GroundTheory.ProfCoh.Involution.tateQuotCongr_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:03:56.36192+00:00
-- url     : https://prove2.me/submissions/2c4c33b5-941e-474d-86f7-125b2df0538a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_RealPlaces_InvolutionDuality

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
open GroundTheory.ProfCoh.Involution
variable {M : Type*} [AddCommGroup M]
variable {σ : M →+ M}
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
namespace GroundTheory.ProfCoh.Involution
theorem _root_.solution (e : M ≃+ N) {σ : M →+ M} {τ : N →+ N} (he : ∀ x, e (σ x) = τ (e x))
    (x : fixedSub σ) :
    tateQuotCongr e he (x : tateQuot σ) = (fixedSubCongr e he x : tateQuot τ) :=
  rfl
end GroundTheory.ProfCoh.Involution
