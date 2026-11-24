-- Prove2me | solution 1 for GroundTheory.ProfCoh.cdp_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:22:47.180409+00:00
-- url     : https://prove2.me/submissions/eb2e1244-1383-416d-b758-4455a8a9eefc

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
    cdp p G ≤ n ↔ ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], IsAddTorsion A →
      ∀ q : ℕ, n < q → AddCommGroup.primaryComponent (cohomology A q) p = ⊥ := by
  refine ⟨fun h A _ hA q hq => ?_, fun h => sInf_le h⟩
  obtain ⟨m, hm, hmq⟩ := sInf_lt_iff.1 (h.trans_lt hq)
  exact hm A hA q hmq
end GroundTheory.ProfCoh
