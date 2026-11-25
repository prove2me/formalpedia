-- Prove2me | solution 1 for GroundTheory.ProfCoh.primaryComponent_eq_bot_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:47:22.547798+00:00
-- url     : https://prove2.me/submissions/31c72ce9-f5ff-4edb-8bea-37423d6e407a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite

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
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {M : Type*} [AddCommGroup M] {p : ℕ} :
    AddCommGroup.primaryComponent M p = ⊥ ↔ ∀ x : M, (∃ k : ℕ, p ^ k • x = 0) → x = 0 := by
  rw [eq_bot_iff]
  exact ⟨fun h x hx => (AddSubgroup.mem_bot).1 (h hx),
    fun h x hx => (AddSubgroup.mem_bot).2 (h x hx)⟩
end GroundTheory.ProfCoh
