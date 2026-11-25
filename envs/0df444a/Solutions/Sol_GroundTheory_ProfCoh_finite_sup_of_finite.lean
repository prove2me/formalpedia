-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_sup_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:07:03.956423+00:00
-- url     : https://prove2.me/submissions/df41145f-0d95-4370-8968-63181fa3d469

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
omit [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (W₁ W₂ : Submodule R M) [Finite W₁] [Finite W₂] : Finite ↥(W₁ ⊔ W₂) := by
  refine Finite.of_surjective
    (fun x : W₁ × W₂ => (⟨x.1 + x.2, Submodule.add_mem_sup x.1.2 x.2.2⟩ : ↥(W₁ ⊔ W₂))) ?_
  rintro ⟨y, hy⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
end GroundTheory.ProfCoh
