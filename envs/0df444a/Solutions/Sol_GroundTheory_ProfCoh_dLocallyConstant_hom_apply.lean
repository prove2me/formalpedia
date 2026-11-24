-- Prove2me | solution 1 for GroundTheory.ProfCoh.dLocallyConstant_hom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:06:06.285422+00:00
-- url     : https://prove2.me/submissions/301eed08-ab36-49ae-9969-0ffd0cabbec7

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
variable [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ)
    (f : locallyConstantCochains A n) :
    ((dLocallyConstant A n).hom f : (Fin (n + 1) → G) → A) =
      (inhomogeneousCochains.d A n).hom f :=
  rfl
end GroundTheory.ProfCoh
