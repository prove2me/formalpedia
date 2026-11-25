-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateMap_g_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:30:56.255308+00:00
-- url     : https://prove2.me/submissions/de05d964-66ca-4831-877f-056fd27708e4

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable {X Y Z : Rep k G}
variable {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
include hS
namespace GroundTheory.GroupCoh
theorem _root_.solution (i : ℤ) : Function.Surjective ((tateComplex.map S.g).f i).hom := by
  have h := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (TateCohomology.map_tateComplexFunctor_shortExact hS) i
  exact (ModuleCat.epi_iff_surjective _).1 h.epi_g
end GroundTheory.GroupCoh
