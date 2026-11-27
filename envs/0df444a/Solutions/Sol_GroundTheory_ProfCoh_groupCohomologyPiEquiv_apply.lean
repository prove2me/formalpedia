-- Prove2me | solution 1 for GroundTheory.ProfCoh.groupCohomologyPiEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:45.147391+00:00
-- url     : https://prove2.me/submissions/cd44ac55-9a27-462a-b14c-167f01eebbbb

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_FilteredHomology
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalClassFormation_IdeleCohomology_Product

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
open CategoryTheory Limits
universe u
variable {k G : Type u} [CommRing k] [Group G] {ι : Type*} {P : Rep.{u} k G}
  {A : ι → Rep.{u} k G}
namespace GroundTheory.ProfCoh
theorem _root_.solution (p : ∀ i, P ⟶ A i)
    (hp : Function.Bijective fun (x : P) (i : ι) => (p i).hom x) (n : ℕ)
    (x : groupCohomology P n) (i : ι) :
    groupCohomologyPiEquiv p hp n x i = (groupCohomology.map (MonoidHom.id G) (p i) n).hom x :=
  rfl
end GroundTheory.ProfCoh
