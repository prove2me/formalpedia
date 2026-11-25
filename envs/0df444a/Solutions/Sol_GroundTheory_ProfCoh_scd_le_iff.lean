-- Prove2me | solution 1 for GroundTheory.ProfCoh.scd_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:34.889046+00:00
-- url     : https://prove2.me/submissions/58c128f0-5194-404e-9bb2-52fa051b3b8d

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt

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
universe u
variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {p G}
namespace GroundTheory.ProfCoh
theorem _root_.solution {n : ℕ∞} : scd G ≤ n ↔ ∀ p : ℕ, p.Prime → scdp p G ≤ n := by
  rw [scd, iSup_le_iff]
  exact ⟨fun h p hp => h ⟨p, hp⟩, fun h p => h p p.prop⟩
end GroundTheory.ProfCoh
