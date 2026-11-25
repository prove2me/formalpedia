-- Prove2me | solution 1 for GroundTheory.ProfCoh.coindCokernelSection_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:24:44.065921+00:00
-- url     : https://prove2.me/submissions/355b494f-a7d5-4c77-b698-4355b84d0b4b

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules

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
open CategoryTheory Filter Topology
universe u
variable (k G : Type u) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [AddCommGroup X] [Module k X]
variable {k G}
namespace GroundTheory.ProfCoh
theorem _root_.solution (A : Rep.{u} k G) [IsDiscreteRep A] (f : LocallyConstant G A) :
    coindCokernelSection A (Submodule.Quotient.mk f) =
      f - (coindEmbedding A).hom (coindEval k G A f) :=
  rfl
end GroundTheory.ProfCoh
