-- Prove2me | solution 1 for GroundTheory.ProfCoh.mem_locallyConstantCochains
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:06:05.845428+00:00
-- url     : https://prove2.me/submissions/20cfd0d8-91f7-41c7-860c-9e97cced5d3f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains

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
open CategoryTheory groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (A : Rep.{u} k G) {n : ℕ} (f : (Fin n → G) → A) :
    f ∈ locallyConstantCochains A n ↔ IsLocallyConstant f :=
  Iff.rfl
end GroundTheory.ProfCoh
