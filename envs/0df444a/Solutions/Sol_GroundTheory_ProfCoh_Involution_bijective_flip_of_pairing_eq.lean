-- Prove2me | solution 1 for GroundTheory.ProfCoh.Involution.bijective_flip_of_pairing_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:50:19.899189+00:00
-- url     : https://prove2.me/submissions/2f2c0f7d-9c36-4c6a-bf3f-8d2f6256df76

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_RealPlaces_InvolutionDuality
import Theorems.Thm_GroundTheory_ProfCoh_Involution_bijective_of_pairing_eq

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
variable {X Y X' Y' : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
namespace GroundTheory.ProfCoh.Involution
theorem _root_.solution (P : X →+ Y →+ QZ) (Q : X' →+ Y' →+ QZ) (e : X' ≃+ X)
    (e' : Y' ≃+ Y) (h : ∀ x y, P (e x) (e' y) = Q x y) (hQ : Function.Bijective Q.flip) :
    Function.Bijective P.flip :=
  bijective_of_pairing_eq P.flip Q.flip e' e (fun y x => h x y) hQ
end GroundTheory.ProfCoh.Involution
