-- Prove2me | solution 1 for GroundTheory.GroupCoh.coinvariantsKer_le_ker_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:53.361855+00:00
-- url     : https://prove2.me/submissions/90288a88-c38d-41a5-a56e-ba742538f3f2

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
import Definitions.Def_GroundTheory_TateCohomology_TateLow

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
open CategoryTheory Limits Representation groupCohomology groupHomology
universe u
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (M : Rep.{u} R G) :
    Coinvariants.ker M.ρ ≤ LinearMap.ker M.ρ.norm := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨g, m⟩, rfl⟩
  simp
end GroundTheory.GroupCoh
