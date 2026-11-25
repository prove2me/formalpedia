-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateMap_f_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:28:14.421206+00:00
-- url     : https://prove2.me/submissions/3b77c3e3-5489-44d7-8120-6c0d14e0e747

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
theorem _root_.solution (i : ℤ) : Function.Injective ((tateComplex.map S.f).f i).hom := by
  have h := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (TateCohomology.map_tateComplexFunctor_shortExact hS) i
  exact (ModuleCat.mono_iff_injective _).1 h.mono_f
end GroundTheory.GroupCoh
