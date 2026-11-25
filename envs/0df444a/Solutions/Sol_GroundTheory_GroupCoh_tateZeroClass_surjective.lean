-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateZeroClass_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:48.449466+00:00
-- url     : https://prove2.me/submissions/9b42576b-9163-4f6d-8337-94a6db6a1407

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (M : Rep.{u} k G) : Function.Surjective (tateZeroClass M) := by
  intro y
  obtain ⟨q, hq⟩ := ((ModuleCat.epi_iff_surjective ((tateCohomologyZeroIso k G).app M).inv).1
    inferInstance) y
  obtain ⟨x, rfl⟩ := (normRangeInvariants M).mkQ_surjective q
  exact ⟨x, hq⟩
end GroundTheory.GroupCoh
