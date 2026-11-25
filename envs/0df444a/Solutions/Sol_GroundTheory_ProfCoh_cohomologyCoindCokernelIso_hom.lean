-- Prove2me | solution 1 for GroundTheory.ProfCoh.cohomologyCoindCokernelIso_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:22:39.864619+00:00
-- url     : https://prove2.me/submissions/4b3e756e-3c53-4862-bbc7-db031bd57dd9

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_Acyclic
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_LongExactSequence
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom

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
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (A : Rep.{u} k G) [IsDiscreteRep A]
namespace GroundTheory.ProfCoh
theorem _root_.solution (n : ℕ) :
    (cohomologyCoindCokernelIso A n).hom = coindδ A (n + 1) :=
  rfl
end GroundTheory.ProfCoh
