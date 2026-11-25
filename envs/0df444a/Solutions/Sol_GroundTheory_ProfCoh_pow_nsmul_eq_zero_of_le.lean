-- Prove2me | solution 1 for GroundTheory.ProfCoh.pow_nsmul_eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:50:21.925079+00:00
-- url     : https://prove2.me/submissions/02e38918-26a4-412d-92a5-5adebca1ef2e

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
theorem _root_.solution {M : Type*} [AddCommMonoid M] {p k K : ℕ} {a : M} (h : k ≤ K)
    (ha : p ^ k • a = 0) : p ^ K • a = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, mul_comm, mul_smul, ha, smul_zero]
end GroundTheory.ProfCoh
