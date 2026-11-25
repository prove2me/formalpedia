-- Prove2me | solution 1 for GroundTheory.ProfCoh.scdp_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:35.940289+00:00
-- url     : https://prove2.me/submissions/2d1d7632-dad4-46c2-a3ff-892cbfb8571e

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
theorem _root_.solution {n : ℕ∞} :
    scdp p G ≤ n ↔ ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A],
      ∀ q : ℕ, n < q → AddCommGroup.primaryComponent (cohomology A q) p = ⊥ := by
  refine ⟨fun h A _ q hq => ?_, fun h => sInf_le h⟩
  obtain ⟨m, hm, hmq⟩ := sInf_lt_iff.1 (h.trans_lt hq)
  exact hm A q hmq
end GroundTheory.ProfCoh
